{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Substitutions where

import Control.Monad
import Control.Monad.State.Strict
import Data.Maybe (mapMaybe)
import Data.Bifunctor.Foldable (bicataM)

import Language.Granule.Context
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr hiding (Substitutable)
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Variables (freshTyVarInContextWithBinding)

import Language.Granule.Utils


{-| Substitutions map from variables to type-level things as defined by
    substitutors -}
type Substitution = Ctxt Substitutors

{-| Substitutors are things we want to substitute in... they may be one
     of several things... -}
data Substitutors =
    SubstT  Type
  | SubstC  Coeffect
  | SubstK  Kind
  deriving (Eq, Show)

instance Pretty Substitutors where
  prettyL l (SubstT t) = "->" <> prettyL l t
  prettyL l (SubstC c) = "->" <> prettyL l c
  prettyL l (SubstK k) = "->" <> prettyL l k

class Substitutable t where
  -- | Rewrite a 't' using a substitution
  substitute :: (?globals :: Globals)
             => Substitution -> t -> Checker t

  unify :: (?globals :: Globals)
        => t -> t -> Checker (Maybe Substitution)

-- Instances for the main representation of things in the types

instance Substitutable Substitutors where

  substitute subst s =
    case s of
      SubstT t -> do
        t <- substitute subst t
        return $ SubstT t

      SubstC c -> do
        c <- substitute subst c
        return $ SubstC c

      SubstK k -> do
        k <- substitute subst k
        return $ SubstK k

  unify (SubstT t) (SubstT t') = unify t t'
  unify (SubstT t) (SubstC c') = do
    -- We can unify a type with a coeffect, if the type is actually a Nat
    k <- inferKindOfType nullSpan t
    k' <- inferCoeffectType nullSpan c'
    case joinKind k (KPromote k') of
      Just (KPromote (TyCon k)) | internalName k == "Nat" -> do
             c <- compileNatKindedTypeToCoeffect nullSpan t
             unify c c'
      _ -> return Nothing
  unify (SubstC c') (SubstT t) = unify (SubstT t) (SubstC c')
  unify (SubstC c) (SubstC c') = unify c c'
  unify (SubstK k) (SubstK k') = unify k k'
  unify _ _ = return Nothing

instance Substitutable Type where
  substitute subst = typeFoldM (baseTypeFold
                              { tfTyVar = varSubst
                              , tfBox = box
                              , tfDiamond = dia })
    where
      box c t = do
        c <- substitute subst c
        mBox c t

      dia e t = do
        e <- substitute subst e
        mDiamond e t

      varSubst v =
         case lookup v subst of
           Just (SubstT t) -> return t
           _               -> mTyVar v

  unify (TyVar v) t = return $ Just [(v, SubstT t)]
  unify t (TyVar v) = return $ Just [(v, SubstT t)]
  unify (FunTy t1 t2) (FunTy t1' t2') = do
    u1 <- unify t1 t1'
    u2 <- unify t2 t2'
    u1 <<>> u2
  unify (TyCon c) (TyCon c') | c == c' = return $ Just []
  unify (Box c t) (Box c' t') = do
    u1 <- unify c c'
    u2 <- unify t t'
    u1 <<>> u2
  unify (Diamond e t) (Diamond e' t') = do
    u1 <- unify e e'
    u2 <- unify t t'
    u1 <<>> u2
  unify (TyApp t1 t2) (TyApp t1' t2') = do
    u1 <- unify t1 t1'
    u2 <- unify t2 t2'
    u1 <<>> u2
  unify (TyInt i) (TyInt j) | i == j = return $ Just []
  unify t@(TyInfix o t1 t2) t'@(TyInfix o' t1' t2') = do
    k <- inferKindOfType nullSpan t
    k' <- inferKindOfType nullSpan t
    case joinKind k k' of
      Just (KPromote (TyCon (internalName -> "Nat"))) -> do
        c  <- compileNatKindedTypeToCoeffect nullSpan t
        c' <- compileNatKindedTypeToCoeffect nullSpan t'
        addConstraint $ Eq nullSpan c c' (TyCon $ mkId "Nat")
        return $ Just []

      _ | o == o' -> do
        u1 <- unify t1 t1'
        u2 <- unify t2 t2'
        u1 <<>> u2
      -- No unification
      _ -> return $ Nothing
  -- No unification
  unify _ _ = return $ Nothing

instance Substitutable Coeffect where

  substitute subst (CPlus c1 c2) = do
      c1' <- substitute subst c1
      c2' <- substitute subst c2
      return $ CPlus c1' c2'

  substitute subst (CJoin c1 c2) = do
      c1' <- substitute subst c1
      c2' <- substitute subst c2
      return $ CJoin c1' c2'

  substitute subst (CMeet c1 c2) = do
      c1' <- substitute subst c1
      c2' <- substitute subst c2
      return $ CMeet c1' c2'

  substitute subst (CTimes c1 c2) = do
      c1' <- substitute subst c1
      c2' <- substitute subst c2
      return $ CTimes c1' c2'

  substitute subst (CMinus c1 c2) = do
      c1' <- substitute subst c1
      c2' <- substitute subst c2
      return $ CMinus c1' c2'

  substitute subst (CExpon c1 c2) = do
      c1' <- substitute subst c1
      c2' <- substitute subst c2
      return $ CExpon c1' c2'

  substitute subst (CInterval c1 c2) = do
      c1' <- substitute subst c1
      c2' <- substitute subst c2
      return $ CInterval c1' c2'

  substitute subst (CProduct c1 c2) = do
      c1' <- substitute subst c1
      c2' <- substitute subst c2
      return $ CProduct c1' c2'

  substitute subst (CVar v) =
      case lookup v subst of
        Just (SubstC c) -> do
           checkerState <- get
           case lookup v (tyVarContext checkerState) of
             -- If the coeffect variable has a poly kind then update it with the
             -- kind of c
             Just ((KVar kv), q) -> do
                k' <- inferCoeffectType nullSpan c
                put $ checkerState { tyVarContext = replace (tyVarContext checkerState)
                                                           v (promoteTypeToKind k', q) }
             _ -> return ()
           return c
        -- Convert a single type substitution (type variable, type pair) into a
        -- coeffect substituion
        Just (SubstT t) -> do
          k <- inferKindOfType nullSpan t
          k' <- inferCoeffectType nullSpan (CVar v)
          case joinKind k (promoteTypeToKind k') of
            Just (KPromote (TyCon (internalName -> "Nat"))) ->
              compileNatKindedTypeToCoeffect nullSpan t
            _ -> return (CVar v)

        _               -> return $ CVar v

  substitute subst (CInfinity k) = do
    k <- substitute subst k
    return $ CInfinity k

  substitute subst (COne k) = do
    k <- substitute subst k
    return $ COne k

  substitute subst (CZero k) = do
    k <- substitute subst k
    return $ CZero k

  substitute subst (CSet tys) = do
    tys <- mapM (\(v, t) -> substitute subst t >>= (\t' -> return (v, t'))) tys
    return $ CSet tys

  substitute subst (CSig c k) = do
    c <- substitute subst c
    k <- substitute subst k
    return $ CSig c k

  substitute _ c@CNat{}      = return c
  substitute _ c@CFloat{}    = return c
  substitute _ c@Level{}     = return c

  unify (CVar v) c = do
    checkerState <- get
    case lookup v (tyVarContext checkerState) of
      -- If the coeffect variable has a poly kind then update it with the
      -- kind of c
      Just ((KVar kv), q) -> do
        k' <- inferCoeffectType nullSpan c
        put $ checkerState { tyVarContext = replace (tyVarContext checkerState)
                                                    v (promoteTypeToKind k', q) }
      Just (k, q) ->
        case c of
          CVar v' -> do
            case lookup v' (tyVarContext checkerState) of
              Just (KVar _, q) ->
                -- The type of v is known and c is a variable with a poly kind
                put $ checkerState { tyVarContext =
                                       replace (tyVarContext checkerState)
                                               v' (k, q) }
              _ -> return ()
          _ -> return ()
      Nothing -> return ()
    -- Standard result of unifying with a variable
    return $ Just [(v, SubstC c)]

  unify c (CVar v) = unify (CVar v) c
  unify (CPlus c1 c2) (CPlus c1' c2') = do
    u1 <- unify c1 c1'
    u2 <- unify c2 c2'
    u1 <<>> u2

  unify (CTimes c1 c2) (CTimes c1' c2') = do
    u1 <- unify c1 c1'
    u2 <- unify c2 c2'
    u1 <<>> u2

  unify (CMeet c1 c2) (CMeet c1' c2') = do
    u1 <- unify c1 c1'
    u2 <- unify c2 c2'
    u1 <<>> u2

  unify (CJoin c1 c2) (CJoin c1' c2') = do
    u1 <- unify c1 c1'
    u2 <- unify c2 c2'
    u1 <<>> u2

  unify (CInfinity k) (CInfinity k') = do
    unify k k'

  unify (CZero k) (CZero k') = do
    unify k k'

  unify (COne k) (COne k') = do
    unify k k'

  unify (CSet tys) (CSet tys') = do
    ums <- zipWithM (\x y -> unify (snd x) (snd y)) tys tys'
    foldM (<<>>) (Just []) ums


  unify (CSig c ck) (CSig c' ck') = do
    u1 <- unify c c'
    u2 <- unify ck ck'
    u1 <<>> u2

  unify c c' =
    if c == c' then return $ Just [] else return Nothing

instance Substitutable Kind where

  substitute subst (KPromote t) = do
      t <- substitute subst t
      return $ KPromote t

  substitute subst KType = return KType
  substitute subst KCoeffect = return KCoeffect
  substitute subst KEffect = return KEffect
  substitute subst KPredicate = return KPredicate
  substitute subst (KFun c1 c2) = do
    c1 <- substitute subst c1
    c2 <- substitute subst c2
    return $ KFun c1 c2
  substitute subst (KVar v) =
    case lookup v subst of
      Just (SubstK k) -> return k
      Just (SubstT t) -> return $ KPromote t
      _               -> return $ KVar v

  unify (KVar v) k =
    return $ Just [(v, SubstK k)]
  unify k (KVar v) =
    return $ Just [(v, SubstK k)]
  unify (KFun k1 k2) (KFun k1' k2') = do
    u1 <- unify k1 k1'
    u2 <- unify k2 k2'
    u1 <<>> u2
  unify k k' = return $ if k == k' then Just [] else Nothing

instance Substitutable t => Substitutable (Maybe t) where
  substitute s Nothing = return Nothing
  substitute s (Just t) = substitute s t >>= return . Just
  unify Nothing _ = return (Just [])
  unify _ Nothing = return (Just [])
  unify (Just x) (Just y) = unify x y


-- | Combine substitutions wrapped in Maybe
(<<>>) :: (?globals :: Globals)
  => Maybe Substitution -> Maybe Substitution -> Checker (Maybe Substitution)
xs <<>> ys =
  case (xs, ys) of
    (Just xs', Just ys') ->
         combineSubstitutions nullSpan xs' ys' >>= (return . Just)
    _ -> return Nothing

-- | Combines substitutions which may fail if there are conflicting
-- | substitutions
combineSubstitutions ::
    (?globals :: Globals)
    => Span -> Substitution -> Substitution -> Checker Substitution
combineSubstitutions sp u1 u2 = do
      -- For all things in the (possibly empty) intersection of contexts `u1` and `u2`,
      -- check whether things can be unified, i.e. exactly
      uss1 <- forM u1 $ \(v, s) ->
        case lookupMany v u2 of
          -- Unifier in u1 but not in u2
          [] -> return [(v, s)]
          -- Possible unificaitons in each part
          alts -> do
              unifs <-
                forM alts $ \s' -> do
                   --(us, t) <- unifiable v t t' t t'
                   us <- unify s s'
                   case us of
                     Nothing -> error "Cannot unify"
                     Just us -> do
                       sUnified <- substitute us s
                       combineSubstitutions sp [(v, sUnified)] us

              return $ concat unifs
      -- Any remaining unifiers that are in u2 but not u1
      uss2 <- forM u2 $ \(v, s) ->
         case lookup v u1 of
           Nothing -> return [(v, s)]
           _       -> return []
      return $ concat uss1 <> concat uss2

{-| Take a context of 'a' and a subhstitution for 'a's (also a context)
  apply the substitution returning a pair of contexts, one for parts
  of the context where a substitution occurred, and one where substitution
  did not occur
>>> let ?globals = mempty in evalChecker initState (runMaybeT $ substCtxt [(mkId "y", SubstT $ TyInt 0)] [(mkId "x", Linear (TyVar $ mkId "x")), (mkId "y", Linear (TyVar $ mkId "y")), (mkId "z", Discharged (TyVar $ mkId "z") (CVar $ mkId "b"))])
Just ([((Id "y" "y"),Linear (TyInt 0))],[((Id "x" "x"),Linear (TyVar (Id "x" "x"))),((Id "z" "z"),Discharged (TyVar (Id "z" "z")) (CVar (Id "b" "b")))])
-}

instance Substitutable (Ctxt Assumption) where

  substitute subst ctxt = do
    (ctxt0, ctxt1) <- substCtxt subst ctxt
    return (ctxt0 <> ctxt1)

  unify = error "Unify not implemented for contexts"

substCtxt :: (?globals :: Globals) => Substitution -> Ctxt Assumption
  -> Checker (Ctxt Assumption, Ctxt Assumption)
substCtxt _ [] = return ([], [])
substCtxt subst ((v, x):ctxt) = do
  (substituteds, unsubstituteds) <- substCtxt subst ctxt
  (v', x') <- substAssumption subst (v, x)

  if (v', x') == (v, x)
    then return (substituteds, (v, x) : unsubstituteds)
    else return ((v, x') : substituteds, unsubstituteds)

substAssumption :: (?globals :: Globals) => Substitution -> (Id, Assumption)
  -> Checker (Id, Assumption)
substAssumption subst (v, Linear t) = do
    t <- substitute subst t
    return (v, Linear t)
substAssumption subst (v, Discharged t c) = do
    t <- substitute subst t
    c <- substitute subst c
    return (v, Discharged t c)


-- | Apply a name map to a type to rename the type variables
renameType :: (?globals :: Globals) => [(Id, Id)] -> Type -> Checker Type
renameType subst = typeFoldM $ baseTypeFold
  { tfBox   = renameBox subst
  , tfTyVar = renameTyVar subst
  }
  where
    renameBox renameMap c t = do
      c' <- substitute (map (\(v, var) -> (v, SubstC $ CVar var)) renameMap) c
      t' <- renameType renameMap t
      return $ Box c' t'
    renameTyVar renameMap v =
      case lookup v renameMap of
        Just v' -> return $ TyVar v'
        -- Shouldn't happen
        Nothing -> return $ TyVar v

-- | Get a fresh polymorphic instance of a type scheme and list of instantiated type variables
-- and their new names.
freshPolymorphicInstance :: (?globals :: Globals)
  => Quantifier   -- Variety of quantifier to resolve universals into (InstanceQ or BoundQ)
  -> Bool         -- Flag on whether this is a data constructor-- if true, then be careful with existentials
  -> TypeScheme   -- Type scheme to freshen
  -> Checker (Type, [Id], [Type])
    -- Returns the type (with skolems), a list of skolem variables, and a list of constraints
freshPolymorphicInstance quantifier isDataConstructor (Forall s kinds constr ty) = do
    -- Universal becomes an existential (via freshCoeffeVar)
    -- since we are instantiating a polymorphic type
    renameMap <- mapM instantiateVariable kinds
    ty <- renameType (elideEither renameMap) ty

    let subst = map (\(v, var) -> (v, SubstT $ TyVar var)) $ elideEither renameMap
    constr' <- mapM (substitute subst) constr

    -- Return the type and all skolem variables
    return (ty, justLefts renameMap, constr')

  where
    -- Freshen variables, create skolem variables
    -- Left of id means a succesful skolem variable created
    -- Right of id means that this is an existential and so a skolem is not generated
    instantiateVariable :: (Id, Kind) -> Checker (Id, Either Id Id)
    instantiateVariable (var, k) =
      if isDataConstructor && (var `notElem` freeVars (resultType ty))
         then do
           -- Signals an existential
           var' <- freshTyVarInContextWithBinding var k ForallQ
           -- Don't return this as a fresh skolem variable
           return (var, Right var')

         else do
           var' <- freshTyVarInContextWithBinding var k quantifier
           return (var, Left var')
    -- Forget the Either
    elideEither = map proj
      where proj (v, Left a) = (v, a)
            proj (v, Right a) = (v, a)
    -- Get just the lefts (used to extract just the skolems)
    justLefts = mapMaybe conv
      where conv (_, Left a) = Just a
            conv (_, Right _) = Nothing

instance Substitutable Pred where
  substitute ctxt =
      predFoldM
        (return . Conj)
        (return . Disj)
        (\ids p1 p2 -> return $ Impl ids p1 p2)
        (\c -> substitute ctxt c >>= return . Con)
        (return . NegPred)
        (\ids k p -> substitute ctxt k >>= \k' -> return $ Exists ids k' p)

  unify _ _ = error "Can't unify predicates"

instance Substitutable Constraint where
  substitute ctxt (Eq s c1 c2 k) = do
    c1 <- substitute ctxt c1
    c2 <- substitute ctxt c2
    k <- substitute ctxt k
    return $ Eq s c1 c2 k

  substitute ctxt (Neq s c1 c2 k) = do
    c1 <- substitute ctxt c1
    c2 <- substitute ctxt c2
    k <- substitute ctxt k
    return $ Neq s c1 c2 k

  substitute ctxt (ApproximatedBy s c1 c2 k) = do
    c1 <- substitute ctxt c1
    c2 <- substitute ctxt c2
    k <- substitute ctxt k
    return $ ApproximatedBy s c1 c2 k

  substitute ctxt (NonZeroPromotableTo s v c k) = do
    c <- substitute ctxt c
    k <- substitute ctxt k
    return $ NonZeroPromotableTo s v c k

  substitute ctxt (Lt s c1 c2) = do
    c1 <- substitute ctxt c1
    c2 <- substitute ctxt c2
    return $ Lt s c1 c2

  substitute ctxt (Gt s c1 c2) = do
    c1 <- substitute ctxt c1
    c2 <- substitute ctxt c2
    return $ Gt s c1 c2

  unify _ _ = error "Can't unify constraints"

instance Substitutable (Equation () Type) where
  substitute ctxt (Equation sp ty patterns expr) =
      do ty' <- substitute ctxt ty
         pat' <- mapM (substitute ctxt) patterns
         expr' <- substitute ctxt expr
         return $ Equation sp ty' pat' expr'
  unify _ _ = error "Can't unify equations"

substituteValue :: (?globals::Globals)
                => Substitution
                -> ValueF ev Type (Value ev Type) (Expr ev Type)
                -> Checker (Value ev Type)
substituteValue ctxt (AbsF ty arg mty expr) =
    do  ty' <- substitute ctxt ty
        arg' <- substitute ctxt arg
        mty' <- mapM (substitute ctxt) mty
        return $ Abs ty' arg' mty' expr
substituteValue ctxt (PromoteF ty expr) =
    do  ty' <- substitute ctxt ty
        return $ Promote ty' expr
substituteValue ctxt (PureF ty expr) =
    do  ty' <- substitute ctxt ty
        return $ Pure ty' expr
substituteValue ctxt (ConstrF ty ident vs) =
    do  ty' <- substitute ctxt ty
        return $ Constr ty' ident vs
substituteValue ctxt (ExtF ty ev) =
    do  ty' <- substitute ctxt ty
        return $ Ext ty' ev
substituteValue _ other = return (ExprFix2 other)

substituteExpr :: (?globals::Globals)
               => Substitution
               -> ExprF ev Type (Expr ev Type) (Value ev Type)
               -> Checker (Expr ev Type)
substituteExpr ctxt (AppF sp ty fn arg) =
    do  ty' <- substitute ctxt ty
        return $ App sp ty' fn arg
substituteExpr ctxt (BinopF sp ty op lhs rhs) =
    do  ty' <- substitute ctxt ty
        return $ Binop sp ty' op lhs rhs
substituteExpr ctxt (LetDiamondF sp ty pattern mty value expr) =
    do  ty' <- substitute ctxt ty
        pattern' <- substitute ctxt pattern
        mty' <- mapM (substitute ctxt) mty
        return $ LetDiamond sp ty' pattern' mty' value expr
substituteExpr ctxt (ValF sp ty value) =
    do  ty' <- substitute ctxt ty
        return $ Val sp ty' value
substituteExpr ctxt (CaseF sp ty expr arms) =
    do  ty' <- substitute ctxt ty
        arms' <- mapM (mapFstM (substitute ctxt)) arms
        return $ Case sp ty' expr arms'

mapFstM :: (Monad m) => (a -> m b) -> (a, c) -> m (b, c)
mapFstM fn (f, r) = do
    f' <- fn f
    return (f', r)

instance Substitutable (Expr () Type) where
  substitute ctxt = bicataM (substituteExpr ctxt) (substituteValue ctxt)
  unify _ _ = error "Can't unify equations"

instance Substitutable (Value () Type) where
  substitute ctxt = bicataM (substituteValue ctxt) (substituteExpr ctxt)
  unify _ _ = error "Can't unify equations"

instance Substitutable (Pattern Type) where
  substitute ctxt = patternFoldM
      (\sp ann nm -> do
          ann' <- substitute ctxt ann
          return $ PVar sp ann' nm)
      (\sp ann -> do
          ann' <- substitute ctxt ann
          return $ PWild sp ann')
      (\sp ann pat -> do
          ann' <- substitute ctxt ann
          return $ PBox sp ann' pat)
      (\sp ann int -> do
          ann' <- substitute ctxt ann
          return $ PInt sp ann' int)
      (\sp ann doub -> do
          ann' <- substitute ctxt ann
          return $ PFloat sp ann' doub)
      (\sp ann nm pats -> do
          ann' <- substitute ctxt ann
          return $ PConstr sp ann' nm pats)

  unify _ _ = error "Can't unify equations"
