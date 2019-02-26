-- Defines the 'Checker' monad used in the type checker
-- and various interfaces for working within this monad

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Granule.Checker.Monad where

import Data.Either (partitionEithers)
import Data.Foldable (toList)
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as M
import Data.Semigroup (sconcat)
import Control.Monad.State.Strict
import Control.Monad.Except
import Control.Monad.Fail (MonadFail)
import Control.Monad.Identity

import Language.Granule.Checker.LaTeX
import Language.Granule.Checker.Predicates
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Context

import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr (Operator, Expr)
import Language.Granule.Syntax.Helpers (FreshenerState(..), freshen)
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Utils

-- State of the check/synth functions
newtype Checker a = Checker
  { unChecker :: ExceptT (NonEmpty CheckerError) (StateT CheckerState IO) a }
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadState CheckerState
    , MonadError (NonEmpty CheckerError)
    , MonadIO
    , MonadFail
    )

type CheckerResult r = Either (NonEmpty CheckerError) r

evalChecker :: CheckerState -> Checker a -> IO (CheckerResult a)
evalChecker initialState (Checker k) = evalStateT (runExceptT k) initialState

runChecker :: CheckerState -> Checker a -> IO (CheckerResult a, CheckerState)
runChecker initialState (Checker k) = runStateT (runExceptT k) initialState

-- | Repeat a checker action for every input value and only fail at the end if
-- any action failed.
runAll :: (a -> Checker b) -> [a] -> Checker [b]
runAll f xs = do
  st <- get
  (results, st) <- liftIO $ runAllCheckers st (map f xs)
  case partitionEithers results of
    ([], successes) -> put st *> pure successes
    -- everything succeeded, so `put` the state and carry on
    (err:errs, _) -> throwError $ sconcat (err:|errs)
    -- combine all errors and fail
  where
    runAllCheckers st [] = pure ([], st)
    runAllCheckers st (c:cs) = do
      (r, st) <- runChecker st c
      (rs,st) <- runAllCheckers st cs
      pure (r:rs, st)

-- | Types of discharged coeffects
data Assumption
  = Linear Type
  | Discharged Type Coeffect
    deriving (Eq, Show)

instance Pretty Assumption where
    prettyL l (Linear ty) = prettyL l ty
    prettyL l (Discharged t c) = ".[" <> prettyL l t <> "]. " <> prettyL l c

instance {-# OVERLAPS #-} Pretty (Id, Assumption) where
   prettyL l (a, b) = prettyL l a <> " : " <> prettyL l b

-- Describes where a pattern is fully consuming, i.e. amounts
-- to linear use and therefore triggers other patterns to be counted
-- as linear, e.g.
--    foo 0 = ..
--    foo _ = ..
-- can be typed as foo : Int ->  because the first means
-- consumption is linear
data Consumption = Full | NotFull deriving (Eq, Show)

-- Given a set of equations, creates an intial vector to describe
-- the consumption behaviour of the patterns (assumes that)
-- the number of patterns is the same for each equation, which
-- is checked elsewhere
initialisePatternConsumptions :: [Equation v a] -> [Consumption]
initialisePatternConsumptions [] = []
initialisePatternConsumptions ((Equation _ _ pats _):_) =
  map (\_ -> NotFull) pats

-- Join information about consumption between branches
joinConsumption :: Consumption -> Consumption -> Consumption
joinConsumption Full _       = Full
joinConsumption _ _          = NotFull

-- Meet information about consumption, across patterns
meetConsumption :: Consumption -> Consumption -> Consumption
meetConsumption NotFull _ = NotFull
meetConsumption _ NotFull = NotFull
meetConsumption Full Full = Full

data CheckerState = CS
            { -- Fresh variable id state
              uniqueVarIdCounterMap  :: M.Map String Nat
            , uniqueVarIdCounter     :: Nat
            -- Local stack of constraints (can be used to build implications)
            , predicateStack :: [Pred]

            -- Stack of a list of additional knowledge from failed patterns/guards
            -- (i.e. from preceding cases) stored as a list of lists ("frames")
            -- tupling a context of locally bound variables and the predicate
            , guardPredicates :: [[((Ctxt Kind, Pred), Span)]]

            -- Type variable context, maps type variables to their kinds
            -- and their quantification
            , tyVarContext   :: Ctxt (Kind, Quantifier)
            -- Context of kind variables and their resolved kind
            -- (used just before solver, to resolve any kind
            -- variables that appear in constraints)
            , kVarContext   :: Ctxt Kind

            -- Guard contexts (all the guards in scope)
            -- which get promoted by branch promotions
            , guardContexts :: [Ctxt Assumption]

            -- Records the amount of consumption by patterns in equation equation
            -- used to work out whether an abstract type has been definitly unified with
            -- and can therefore be linear
            , patternConsumption :: [Consumption]

            -- Data type information
            , typeConstructors :: Ctxt (Kind, Cardinality) -- the kind of the and number of data constructors
            , dataConstructors :: Ctxt TypeScheme

            -- LaTeX derivation
            , deriv      :: Maybe Derivation
            , derivStack :: [Derivation]

            -- Warning accumulator
            -- , warnings :: [Warning]
            }
  deriving (Show, Eq) -- for debugging

-- | Initial checker context state
initState :: CheckerState
initState = CS { uniqueVarIdCounterMap = M.empty
               , uniqueVarIdCounter = 0
               , predicateStack = []
               , guardPredicates = [[]]
               , tyVarContext = []
               , kVarContext = []
               , guardContexts = []
               , patternConsumption = []
               , typeConstructors = Primitives.typeConstructors
               , dataConstructors = Primitives.dataConstructors
               , deriv = Nothing
               , derivStack = []
               }

-- *** Various helpers for manipulating the context


{- | Given a computation in the checker monad, peek the result without
actually affecting the current checker environment. Unless the value is
discarded, the rhs result computation must be run! This is useful for
example when resolving overloaded operators, where we don't want to report
unification errors that arise during operator resultion to the user.
-}
peekChecker :: Checker a -> Checker (CheckerResult a, Checker ())
peekChecker k = do
  checkerState <- get
  (result, localState) <- liftIO $ runChecker checkerState k
  pure (result, put localState)

pushGuardContext :: Ctxt Assumption -> Checker ()
pushGuardContext ctxt = do
  modify (\state ->
    state { guardContexts = ctxt : guardContexts state })

popGuardContext :: Checker (Ctxt Assumption)
popGuardContext = do
  state <- get
  let (c, cs) = case guardContexts state of
                  (c:cs) -> (c,cs)
                  [] -> error "Internal error. Empty guard context."
  put (state { guardContexts = cs })
  return c

allGuardContexts :: Checker (Ctxt Assumption)
allGuardContexts = concat . guardContexts <$> get

-- | Start a new conjunction frame on the predicate stack
newConjunct :: Checker ()
newConjunct = do
  checkerState <- get
  put (checkerState { predicateStack = Conj [] : predicateStack checkerState })

-- | Creates a new "frame" on the stack of information about failed cases
-- | This happens when we start a case expression
newCaseFrame :: Checker ()
newCaseFrame =
  modify (\st -> st { guardPredicates = [] : guardPredicates st } )

-- | Pop (and don't return) the top of the failed case knowledge stack
-- | This happens when we finish a case expression
popCaseFrame :: Checker ()
popCaseFrame =
  modify (\st -> st { guardPredicates = tail (guardPredicates st) })

-- | Takes the top two conjunction frames and turns them into an
-- impliciation
-- The first parameter is a list of any
-- existential variables being introduced in this implication
concludeImplication :: (?globals :: Globals) => Span -> [Id] -> Checker ()
concludeImplication s localVars = do
  checkerState <- get
  case predicateStack checkerState of
    (p' : p : stack) -> do

       -- Get all the kinds for the local variables
       localCtxt <- forM localVars $ \v ->
                      case lookup v (tyVarContext checkerState) of
                        Just (k, _) -> return (v, k)
                        Nothing -> error $ "I don't know the kind of "
                                          <> pretty v <> " in "
                                          <> pretty (tyVarContext checkerState)

       case guardPredicates checkerState of

        [] -> error "Internal bug: Guard predicate is [] and should not be"

        -- No previous guards in the current frame to provide additional information
        [] : knowledgeStack -> do
          let impl = Impl localVars p p'

          -- Add the implication to the predicate stack
          modify (\st -> st { predicateStack = pushPred impl stack
          -- And add this case to the knowledge stack
                            , guardPredicates = [((localCtxt, p), s)] : knowledgeStack })

        -- Some information currently in the stack frame
        previousGuards : knowledgeStack -> do

           let previousGuardCtxt = concatMap (fst . fst) previousGuards
           let prevGuardPred = Conj (map (snd . fst) previousGuards)

           -- negation of the previous guard
           let guard' = foldr (uncurry Exists) (NegPred prevGuardPred) previousGuardCtxt
           guard <- freshenPred guard'

           -- Implication of p .&& negated previous guards => p'
           let impl = if (isTrivial prevGuardPred)
                        then Impl localVars p p'
                        else Impl localVars (Conj [p, guard]) p'

           let knowledge = ((localCtxt, p), s) : previousGuards

           -- Store `p` (impliciation antecedent) to use in later cases
           -- on the top of the guardPredicates stack
           modify (\st -> st { predicateStack = pushPred impl stack
           -- And add this case to the knowledge stack
                             , guardPredicates = knowledge : knowledgeStack })


    _ -> error "Predicate: not enough conjunctions on the stack"

freshenPred :: Pred -> Checker Pred
freshenPred pred = do
    st <- get
    -- Run the freshener using the checkers unique variable id
    let (pred', freshenerState) =
         runIdentity $ runStateT (freshen pred)
          (FreshenerState { counter = 1 + uniqueVarIdCounter st, varMap = [], tyMap = []})
    -- Update the unique counter in the checker
    put (st { uniqueVarIdCounter = counter freshenerState })
    return pred'
{-
-- Create a local existential scope
-- NOTE: leaving this here, but this approach is not used and is incompataible
-- with the way that existential variables are generated in the solver
--
existential :: (?globals :: Globals) => Id -> Kind -> Checker ()
existential var k = do
  case k of
    -- No need to add variables of kind Type to the predicate
    KType -> return ()
    k -> do
      checkerState <- get
      case predicateStack checkerState of
        (p : stack) -> do
          put (checkerState { predicateStack = Exists var k p : stack })
-}

pushPred :: Pred -> [Pred] -> [Pred]
pushPred p (p' : stack) = appendPred p p' : stack
pushPred p [] = [Conj [p]]

appendPred :: Pred -> Pred -> Pred
appendPred p (Conj ps) = Conj (p : ps)
appendPred p (Exists var k ps) = Exists var k (appendPred p ps)
appendPred _ p = error $ "Cannot append a predicate to " <> show p

addPredicate :: Pred -> Checker ()
addPredicate p = do
  checkerState <- get
  case predicateStack checkerState of
    (p' : stack) ->
      put (checkerState { predicateStack = appendPred p p' : stack })
    stack ->
      put (checkerState { predicateStack = Conj [p] : stack })

-- | A helper for adding a constraint to the context
addConstraint :: Constraint -> Checker ()
addConstraint c = do
  checkerState <- get
  case predicateStack checkerState of
    (p : stack) ->
      put (checkerState { predicateStack = appendPred (Con c) p : stack })
    stack ->
      put (checkerState { predicateStack = Conj [Con c] : stack })

-- | A helper for adding a constraint to the previous frame (i.e.)
-- | if I am in a local context, push it to the global
addConstraintToPreviousFrame :: Constraint -> Checker ()
addConstraintToPreviousFrame c = do
        checkerState <- get
        case predicateStack checkerState of
          (ps : ps' : stack) ->
            put (checkerState { predicateStack = ps : (appendPred (Con c) ps') : stack })
          (ps : stack) ->
            put (checkerState { predicateStack = ps : Conj [Con c] : stack })
          stack ->
            put (checkerState { predicateStack = Conj [Con c] : stack })

throw :: CheckerError -> Checker a
throw = throwError . pure

illLinearityMismatch :: Span -> NonEmpty LinearityMismatch -> Checker a
illLinearityMismatch sp ms = throwError $ fmap (LinearityError sp) ms

{- Helpers for error messages and checker control flow -}
data CheckerError
  = TypeError
    { errLoc :: Span, tyExpected :: Type, tyActual :: Type }
  | GradingError
    { errLoc :: Span, errConstraint :: Neg Constraint }
  | KindMismatch
    { errLoc :: Span, kExpected :: Kind, kActual :: Kind }
  | KindError
    { errLoc :: Span, errTy :: Type, errK :: Kind }
  | IntervalGradeKindError
    { errLoc :: Span, errTy1 :: Type, errTy2 :: Type }
  | LinearityError
    { errLoc :: Span, linearityMismatch :: LinearityMismatch }
  | PatternTypingError
    { errLoc :: Span, errPat :: Pattern (), tyExpected :: Type }
  | PatternTypingMismatch
    { errLoc :: Span, errPat :: Pattern (), tyExpected :: Type, tyActual :: Type }
  | PatternArityError
    { errLoc :: Span, errId :: Id }
  | UnboundVariableError
    { errLoc :: Span, errId :: Id }
  | UnboundTypeVariable
    { errLoc :: Span, errId :: Id }
  | RefutablePatternError
    { errLoc :: Span, errPat :: Pattern () }
  | TypeConstructorNameClash -- TODO: duplicate?
    { errLoc :: Span, errId :: Id }
  | DuplicatePatternError
    { errLoc :: Span, duplicateBinder :: String }
  | UnificationError
    { errLoc :: Span, errTy1 :: Type, errTy2 :: Type }
  | UnificationKindError
    { errLoc :: Span, errTy1 :: Type, errK1 :: Kind, errTy2 :: Type, errK2 :: Kind }
  | TypeVariableMismatch
    { errLoc :: Span, errVar :: Id, errTy1 :: Type, errTy2 :: Type }
  | UndefinedEqualityKindError
    { errLoc :: Span, errTy1 :: Type, errK1 :: Kind, errTy2 :: Type, errK2 :: Kind }
  | CoeffectUnificationError
    { errLoc :: Span, errTy1 :: Type, errTy2 :: Type, errC1 :: Coeffect, errC2 :: Coeffect }
  | DataConstructorTypeVariableNameClash
    { errLoc :: Span, errDataConstructorId :: Id, errTypeConstructor :: Id, errVar :: Id }
  | DataConstructorNameClashError
    { errLoc :: Span, errId :: Id }
  | EffectMismatch
    { errLoc :: Span, effExpected :: Type, effActual :: Type }
  | UnificationDisallowed
    { errLoc :: Span, errTy1 :: Type, errTy2 :: Type }
  | MonoUnificationFail
    { errLoc :: Span, errVar :: Id, errTy :: Type }
  | UnificationFail
    { errLoc :: Span, errVar :: Id, errTy :: Type }
  | SessionDualityError
    { errLoc :: Span, errTy1 :: Type, errTy2 :: Type }
  | NoUpperBoundError
    { errLoc :: Span, errTy1 :: Type, errTy2 :: Type }
  | DisallowedCoeffectNesting
    { errLoc :: Span, errTyOuter :: Type, errTyInner :: Type }
  | UnboundDataConstructor
    { errLoc :: Span, errId :: Id }
  | UnboundTypeConstructor
    { errLoc :: Span, errId :: Id }
  | TooManyPatternsError
    { errLoc :: Span, errPats :: NonEmpty (Pattern ()), tyExpected :: Type, tyActual :: Type }
  | DataConstructorReturnTypeError
    { errLoc :: Span, idExpected :: Id, idActual :: Id }
  | MalformedDataConstructorType
    { errLoc :: Span, errTy :: Type }
  | ExpectedEffectType
    { errLoc :: Span, errTy :: Type }
  | LhsOfApplicationNotAFunction
    { errLoc :: Span, errTy :: Type }
  | FailedOperatorResolution
    { errLoc :: Span, errOp :: Operator, errTy :: Type }
  | NeedTypeSignature
    { errLoc :: Span, errExpr :: Expr () () }
  | SolverErrorCounterExample
    { errLoc :: Span, errDefId :: Id, errPred :: Pred }
  | SolverErrorFalsifiableTheorem
    { errLoc :: Span, errDefId :: Id, errPred :: Pred }
  | SolverError
    { errLoc :: Span, errMsg :: String }
  | SolverTimeout
    { errLoc :: Span, errSolverTimeoutMillis :: Integer }
  | UnifyGradedLinear
    { errLoc :: Span, errGraded :: Id, errLinear :: Id }
  | PatternUnreachable -- TODO: make proper structured error once this has been implemented for real
    { errLoc :: Span, errMsg :: String }
  | NameClashTypeConstructors -- we arbitrarily use the second thing that clashed as the error location
    { errLoc :: Span, errDataDecl :: DataDecl, otherDataDecls :: NonEmpty DataDecl }
  | NameClashDataConstructors -- we arbitrarily use the second thing that clashed as the error location
    { errLoc :: Span, errDataConstructor :: DataConstr, otherDataConstructors :: NonEmpty DataConstr }
  | NameClashDefs -- we arbitrarily use the second thing that clashed as the error location
    { errLoc :: Span, errDef :: Def () (), otherDefs :: NonEmpty (Def () ()) }
  deriving (Show, Eq)


instance UserMsg CheckerError where
  location = errLoc

  title TypeError{} = "Type error"
  title GradingError{} = "Grading error"
  title KindMismatch{} = "Kind mismatch"
  title KindError{} = "Kind error"
  title IntervalGradeKindError{} = "Interval kind error"
  title LinearityError{} = "Linearity error"
  title PatternTypingError{} = "Pattern typing error"
  title PatternTypingMismatch{} = "Pattern typing mismatch"
  title PatternArityError{} = "Pattern arity error"
  title UnboundVariableError{} = "Unbound variable error"
  title UnboundTypeVariable{} = "Unbound type variable"
  title RefutablePatternError{} = "Pattern is refutable"
  title TypeConstructorNameClash{} = "Type constructor name clash"
  title DataConstructorTypeVariableNameClash{} = "Type variable name clash"
  title DuplicatePatternError{} = "Duplicate pattern"
  title UnificationError{} = "Unification error"
  title UnificationKindError{} = "Unification kind error"
  title TypeVariableMismatch{} = "Type variable mismatch"
  title UndefinedEqualityKindError{} = "Undefined kind equality"
  title CoeffectUnificationError{} = "Coeffect unification error"
  title DataConstructorNameClashError{} = "Data constructor name clash"
  title EffectMismatch{} = "Effect mismatch"
  title UnificationDisallowed{} = "Unification disallowed"
  title UnificationFail{} = "Unification failed"
  title MonoUnificationFail{} = "Unification failed"
  title SessionDualityError{} = "Session duality error"
  title NoUpperBoundError{} = "Type upper bound"
  title DisallowedCoeffectNesting{} = "Bad coeffect nesting"
  title UnboundDataConstructor{} = "Unbound data constructor"
  title UnboundTypeConstructor{} = "Unbound type constructor"
  title TooManyPatternsError{} = "Too many patterns"
  title DataConstructorReturnTypeError{} = "Wrong return type in data constructor"
  title MalformedDataConstructorType{} = "Malformed data constructor type"
  title ExpectedEffectType{} = "Type error"
  title LhsOfApplicationNotAFunction{} = "Type error"
  title FailedOperatorResolution{} = "Operator resolution failed"
  title NeedTypeSignature{} = "Type signature needed"
  title SolverErrorCounterExample{} = "Counter example"
  title SolverErrorFalsifiableTheorem{} = "Falsifiable theorem"
  title SolverError{} = "Solver error"
  title SolverTimeout{} = "Solver timeout"
  title UnifyGradedLinear{} = "Type error"
  title PatternUnreachable{} = "Pattern unreachable"
  title NameClashTypeConstructors{} = "Type constructor name clash"
  title NameClashDataConstructors{} = "Data constructor name clash"
  title NameClashDefs{} = "Definition name clash"

  msg TypeError{..} = if pretty tyExpected == pretty tyActual
    then "Expected `" <> pretty tyExpected <> "` but got `" <> pretty tyActual <> "` coming from a different binding"
    else "Expected `" <> pretty tyExpected <> "` but got `" <> pretty tyActual <> "`"

  msg GradingError{..} = pretty errConstraint

  msg KindMismatch{..}
    = "Expected kind `" <> pretty kExpected <> "` but got `" <> pretty kActual <> "`"

  msg KindError{..}
    = "Type `" <> pretty errTy
    <> "` does not have expected kind `" <> pretty errK <> "`"

  msg IntervalGradeKindError{..}
   = "Interval grade mismatch `" <> pretty errTy1 <> "` and `" <> pretty errTy2 <> "`"

  msg LinearityError{..} = case linearityMismatch of
    LinearUsedMoreThanOnce v ->
      "Linear variable `" <> pretty v <> "` is used more than once."
    LinearNotUsed v ->
      "Linear variable `" <> pretty v <> "` is never used."
    LinearUsedNonLinearly v ->
      "Variable `" <> pretty v
      <> "` is promoted but its binding is linear; its binding should be under a box."
    NonLinearPattern ->
      "Wildcard pattern `_` allowing a value to be discarded"

  msg PatternTypingError{..}
    = "Pattern match `"
    <> pretty errPat
    <> "` does not have expected type `"
    <> pretty tyExpected
    <> "`"

  msg PatternTypingMismatch{..}
    = "Expected type `"
    <> pretty tyExpected
    <> "` but got `"
    <> pretty tyActual
    <> "` in pattern `"
    <> pretty errPat
    <> "`"

  msg PatternArityError{..}
    = "Data constructor `"
      <> pretty errId
      <> "` is applied to too many arguments."

  msg UnboundVariableError{..} = "`" <> pretty errId <> "`"

  msg UnboundTypeVariable{..}
    = "`" <> pretty errId <> "` is not quantified"

  msg RefutablePatternError{..}
    = "Pattern match " <> pretty errPat
    <> " can fail; only irrefutable patterns allowed in this context"

  msg TypeConstructorNameClash{..}
    = "Type constructor `" <> pretty errId <> "` already defined"

  msg DataConstructorTypeVariableNameClash{..} = mconcat
    [ "Type variable "
    , pretty errVar
    , " in data constructor `"
    , pretty errDataConstructorId
    , "` are already bound by the associated type constructor `"
    , pretty errTypeConstructor
    , "`. Choose different, unbound names."
    ]

  msg DuplicatePatternError {..}
    = "Variable `" <> duplicateBinder <> "` bound more than once"

  msg UnificationError{..} = if pretty errTy1 == pretty errTy2
    then "Type `" <> pretty errTy1 <> "` is not unifiable with the type `" <> pretty errTy2 <> "` coming from a different binding"
    else "Type `" <> pretty errTy1 <> "` is not unifiable with the type `" <> pretty errTy2 <> "`"

  msg (UnificationKindError _ t1 k1 t2 k2)
    = "Trying to unify a type `"
    <> pretty t1 <> "` of kind " <> pretty k1
    <> " with a type `"
    <> pretty t2 <> "` of kind " <> pretty k2

  msg TypeVariableMismatch{..}
    = "Variable " <> pretty errVar <> " is being used at two conflicting types "
    <> "`" <> pretty errTy1 <> "` and `" <> pretty errTy2 <> "`"

  msg UndefinedEqualityKindError{..}
    = "Equality is not defined between kinds "
    <> pretty errK1 <> " and " <> pretty errK2
    <> "\t\n from equality "
    <> "'" <> pretty errTy2 <> "' and '" <> pretty errTy1 <> "' equal."

  msg CoeffectUnificationError{..}
    = "Cannot unify coeffect types '"
    <> pretty errTy1 <> "' and '" <> pretty errTy2
    <> "' for coeffects `" <> pretty errC1 <> "` and `" <> pretty errC2 <> "`"

  msg DataConstructorNameClashError{..}
    = "Data constructor `" <> pretty errId <> "` already defined."

  msg EffectMismatch{..}
    = "Expected `" <> pretty effExpected
    <> "`, but got `" <> pretty effActual <> "`"

  msg UnificationDisallowed{..}
    = "Trying to unify `"
    <> pretty errTy1 <> "` and `"
    <> pretty errTy2 <> "` but in a context where unification is not allowed."

  msg UnificationFail{..}
    = "Type `" <> pretty errTy <> "` is not unifiable with `" <> pretty errVar <> "`"

  msg MonoUnificationFail{..}
    = "Trying to match a polymorphic type  `" <> pretty errVar <> "` with monomorphic type `" <> pretty errTy <> "`"

  msg SessionDualityError{..}
    = "Session type `" <> pretty errTy1 <> "` is not dual to `" <> pretty errTy2 <> "`"

  msg NoUpperBoundError{..}
    = "Types `" <> pretty errTy1 <> "` and `"
    <> pretty errTy2 <> "` have no upper bound"

  msg DisallowedCoeffectNesting{..}
    = "Graded modalities of outer index type `" <> pretty errTyOuter
    <> "` and inner type `" <> pretty errTyInner <> "` cannot be nested"

  msg UnboundDataConstructor{..}
    = "`" <> pretty errId <> "`"

  msg UnboundTypeConstructor{..}
    = "`" <> pretty errId <> "`"

  msg TooManyPatternsError{..}
    = "Couldn't match expected type `"
    <> pretty tyExpected
    <> "` against a type of the form `"
    <> pretty tyActual
    <> "` implied by the remaining pattern(s)\n\t"
    <> (intercalate "\n\t" . map (ticks . pretty) . toList) errPats

  msg DataConstructorReturnTypeError{..}
    = "Expected type constructor `" <> pretty idExpected
    <> "`, but got `" <> pretty idActual <> "`"

  msg MalformedDataConstructorType{..}
    = "`" <> pretty errTy <> "` not valid in a data constructor definition"

  msg ExpectedEffectType{..}
    = "Expected an effect type but got `" <> pretty errTy <> "` in subject of let"

  msg LhsOfApplicationNotAFunction{..}
    = "Expected a function type on the left-hand side of an application, but got `"
    <> pretty errTy <> "`"

  msg FailedOperatorResolution{..}
    = "Could not resolve operator `" <> pretty errOp
    <> "` at type `" <> pretty errTy <> "`"

  msg NeedTypeSignature{..}
    = "The type could not be inferred, please add a type signature to expression `"
    <> pretty errExpr <> "`"

  msg SolverErrorCounterExample{..}
    =  "The following theorem associated with `" <> pretty errDefId
    <> "` is falsifiable:\n\t"
    <> pretty errPred

  msg SolverErrorFalsifiableTheorem{..}
    =  "The following theorem associated with `" <> pretty errDefId
    <> "` is falsifiable:\n\t"
    <> pretty errPred

  msg SolverError{..} = errMsg

  msg SolverTimeout{..}
    = "Solver timed out with limit of " <> show errSolverTimeoutMillis
    <> " ms. You may want to increase the timeout (see --help)."

  msg UnifyGradedLinear{..}
    = "Can't unify free-variable types:\n\t"
    <> "(graded) " <> pretty errGraded
    <> "\n  with\n\t(linear) " <> pretty errLinear

  msg PatternUnreachable{..} = errMsg

  msg NameClashTypeConstructors{..}
    = "`" <> pretty (dataDeclId errDataDecl) <> "` already defined at\n\t"
    <> (intercalate "\n\t" . map (pretty . dataDeclSpan) . toList) otherDataDecls

  msg NameClashDataConstructors{..}
    = "`" <> pretty (dataConstrId errDataConstructor) <> "` already defined at\n\t"
    <> (intercalate "\n\t" . map (pretty . dataConstrSpan) . toList) otherDataConstructors

  msg NameClashDefs{..}
    = "`" <> pretty (defId errDef) <> "` already defined at\n\t"
    <> (intercalate "\n\t" . map (pretty . defSpan) . toList) otherDefs

data LinearityMismatch
  = LinearNotUsed Id
  | LinearUsedNonLinearly Id
  | NonLinearPattern
  | LinearUsedMoreThanOnce Id
  deriving (Eq, Show) -- for debugging
