-- Mainly provides a kind checker on types

module Language.Granule.Checker.Kinds (kindCheckDef
                    , inferKindOfType
                    , inferKindOfType'
                    , joinCoeffectTypes
                    , hasLub
                    , joinKind
                    , inferCoeffectType
                    , inferCoeffectTypeAssumption
                    , mguCoeffectTypes
                    , promoteTypeToKind
                    , demoteKindToType) where

import Control.Monad.State.Strict
import Data.Foldable (foldrM)

import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates
import Language.Granule.Checker.Primitives (tyOps)
import Language.Granule.Checker.Variables
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Context
import Language.Granule.Utils



promoteTypeToKind :: Type -> Kind
promoteTypeToKind (TyVar v) = KVar v
promoteTypeToKind t = KPromote t

demoteKindToType :: Kind -> Maybe Type
demoteKindToType (KPromote t) = Just t
demoteKindToType (KVar v)     = Just (TyVar v)
demoteKindToType _            = Nothing

-- Currently we expect that a type scheme has kind KType
kindCheckDef :: (?globals :: Globals) => Def v t -> Checker ()
kindCheckDef (Def s _ _ (Forall _ quantifiedVariables constraints ty)) = do
  -- Set up the quantified variables in the type variable context
  modify (\st -> st { tyVarContext = map (\(n, c) -> (n, (c, ForallQ))) quantifiedVariables})

  forM_ constraints $ \constraint -> do
    kind <- inferKindOfType' s quantifiedVariables constraint
    case kind of
      KPredicate -> return ()
      _ -> throw KindMismatch{ errLoc = s, kExpected = KPredicate, kActual = kind }

  kind <- inferKindOfType' s quantifiedVariables ty
  case kind of
    KType -> modify (\st -> st { tyVarContext = [] })
    KPromote (TyCon k) | internalName k == "Protocol" -> modify (\st -> st { tyVarContext = [] })
    _     -> throw KindMismatch{ errLoc = s, kExpected = KType, kActual = kind }

inferKindOfType :: (?globals :: Globals) => Span -> Type -> Checker Kind
inferKindOfType s t = do
    checkerState <- get
    inferKindOfType' s (stripQuantifiers $ tyVarContext checkerState) t

inferKindOfType' :: (?globals :: Globals) => Span -> Ctxt Kind -> Type -> Checker Kind
inferKindOfType' s quantifiedVariables t =
    typeFoldM (TypeFold kFun kCon kBox kDiamond kVar kApp kInt kInfix kSet) t
  where
    kFun (KPromote (TyCon c)) (KPromote (TyCon c'))
     | internalName c == internalName c' = return $ kConstr c

    kFun KType KType = return KType
    -- kFun KType (KPromote (TyCon (internalName -> "Protocol"))) = return $ KPromote (TyCon (mkId "Protocol")) -- TODO
    kFun KType y = throw KindMismatch{ errLoc = s, kExpected = KType, kActual = y }
    kFun x _     = throw KindMismatch{ errLoc = s, kExpected = KType, kActual = x }
    kCon conId = do
        st <- get
        case lookup conId (typeConstructors st) of
          Just (kind,_) -> return kind
          Nothing   -> case lookup conId (dataConstructors st) of
            Just (Forall _ [] [] t) -> return $ KPromote t
            Just _ -> error $ pretty s <> "I'm afraid I can't yet promote the polymorphic data constructor:"  <> pretty conId
            Nothing -> throw UnboundTypeConstructor{ errLoc = s, errId = conId }

    kBox c KType = do
       -- Infer the coeffect (fails if that is ill typed)
       _ <- inferCoeffectType s c
       return KType
    kBox _ x = throw KindMismatch{ errLoc = s, kExpected = KType, kActual = x }

    kDiamond ke kt = do
      unless (ke == KEffect)
        (throw KindMismatch{ errLoc = s, kExpected = KEffect, kActual = ke })
      case kt of
        KType -> return KType
        _ -> throw KindMismatch{ errLoc = s, kExpected = KType, kActual = kt }

    kVar tyVar =
      case lookup tyVar quantifiedVariables of
        Just kind -> return kind
        Nothing   -> do
          st <- get
          case lookup tyVar (kVarContext st) of
            Just kind -> return kind
            Nothing ->
              throw UnboundTypeVariable{ errLoc = s, errId = tyVar }

    kApp (KFun k1 k2) kArg | k1 `hasLub` kArg = return k2
    kApp k kArg = throw KindMismatch
        { errLoc = s
        , kExpected = (KFun kArg (KVar $ mkId "..."))
        , kActual = k
        }

    kInt _ = return $ kConstr $ mkId "Nat"

    kInfix (tyOps -> (k1exp, k2exp, kret)) k1act k2act
      | not (k1act `hasLub` k1exp) = throw
        KindMismatch{ errLoc = s, kExpected = k1exp, kActual = k1act}
      | not (k2act `hasLub` k2exp) = throw
        KindMismatch{ errLoc = s, kExpected = k2exp, kActual = k2act}
      | otherwise                  = pure kret

    kSet :: [Kind] -> Checker Kind
    kSet [] = KPromote . TyApp (TyCon "Set") $ KEffect
    kSet (k:ks)
      = KPromote
      . TyApp (TyCon "Set")
      . maybe undefined demoteKindToType
      <$> foldrM go k ks
      where
        go k1 k2 = case joinKind k1 k2 of
          Just k -> pure k
          Nothing -> throw
            KindMismatch{ errLoc = s, kExpected = k1, kActual = k2}

-- | Compute the join of two kinds, if it exists
joinKind :: Kind -> Kind -> Maybe Kind
joinKind k1 k2 | k1 == k2 = Just k1
joinKind (KPromote t1) (KPromote t2) =
   fmap KPromote (joinCoeffectTypes t1 t2)
joinKind _ _ = Nothing

-- | Some coeffect types can be joined (have a least-upper bound). This
-- | function computes the join if it exists.
joinCoeffectTypes :: Type -> Type -> Maybe Type
joinCoeffectTypes t1 t2 = case (t1, t2) of
  -- Equal things unify to the same thing
  (t, t') | t == t' -> Just t

  -- `Nat` can unify with `Q` to `Q`
  (TyCon (internalName -> "Q"), TyCon (internalName -> "Nat")) ->
        Just $ TyCon $ mkId "Q"

  (TyCon (internalName -> "Nat"), TyCon (internalName -> "Q")) ->
        Just $ TyCon $ mkId "Q"

  -- `Nat` can unify with `Ext Nat` to `Ext Nat`
  (t, TyCon (internalName -> "Nat")) | t == extendedNat ->
        Just extendedNat
  (TyCon (internalName -> "Nat"), t) | t == extendedNat ->
        Just extendedNat

  (TyApp t1 t2, TyApp t1' t2') ->
    TyApp <$> joinCoeffectTypes t1 t1' <*> joinCoeffectTypes t2 t2'

  _ -> Nothing

-- | Predicate on whether two kinds have a least upper bound
-- TODO I'm assuming this is commutative? We should have a property test for
-- this @buggymcbugfix
hasLub :: Kind -> Kind -> Bool
hasLub k1 k2 =
  case joinKind k1 k2 of
    Nothing -> False
    Just _  -> True


-- | Infer the type of ta coeffect term (giving its span as well)
inferCoeffectType :: (?globals :: Globals) => Span -> Coeffect -> Checker Type

-- Coeffect constants have an obvious kind
inferCoeffectType _ (Level _)         = return $ TyCon $ mkId "Level"
inferCoeffectType _ (CNat _)          = return $ TyCon $ mkId "Nat"
inferCoeffectType _ (CFloat _)        = return $ TyCon $ mkId "Q"
inferCoeffectType _ (CSet _)          = return $ TyCon $ mkId "Set"
inferCoeffectType s (CProduct c1 c2)    = do
  k1 <- inferCoeffectType s c1
  k2 <- inferCoeffectType s c2
  return $ TyApp (TyApp (TyCon $ mkId "×") k1) k2

inferCoeffectType s (CInterval c1 c2)    = do
  k1 <- inferCoeffectType s c1
  k2 <- inferCoeffectType s c2

  case joinCoeffectTypes k1 k2 of
    Just k -> return $ TyApp (TyCon $ mkId "Interval") k

    Nothing -> throw IntervalGradeKindError{ errLoc = s, errTy1 = k1, errTy2 = k2 }

-- Take the join for compound coeffect epxressions
inferCoeffectType s (CPlus c c')  = mguCoeffectTypes s c c'
inferCoeffectType s (CMinus c c') = mguCoeffectTypes s c c'
inferCoeffectType s (CTimes c c') = mguCoeffectTypes s c c'
inferCoeffectType s (CMeet c c')  = mguCoeffectTypes s c c'
inferCoeffectType s (CJoin c c')  = mguCoeffectTypes s c c'
inferCoeffectType s (CExpon c c') = mguCoeffectTypes s c c'

-- Coeffect variables should have a type in the cvar->kind context
inferCoeffectType s (CVar cvar) = do
  st <- get
  case lookup cvar (tyVarContext st) of
    Nothing -> do
      throw UnboundTypeVariable{ errLoc = s, errId = cvar }
--      state <- get
--      let newType = TyVar $ "ck" <> show (uniqueVarId state)
      -- We don't know what it is yet though, so don't update the coeffect kind ctxt
--      put (state { uniqueVarId = uniqueVarId state + 1 })
--      return newType

    Just (KVar   name, _) -> return $ TyVar name
    Just (KPromote t, _)  -> checkKindIsCoeffect s t
    Just (k, _)           -> throw
      KindMismatch{ errLoc = s, kExpected = KCoeffect, kActual = k }

inferCoeffectType s (CZero t) = checkKindIsCoeffect s t
inferCoeffectType s (COne t)  = checkKindIsCoeffect s t
inferCoeffectType s (CInfinity (Just t)) = checkKindIsCoeffect s t
-- Unknown infinity defaults to the interval of extended nats version
inferCoeffectType s (CInfinity Nothing) = return (TyApp (TyCon $ mkId "Interval") extendedNat)
inferCoeffectType s (CSig _ t) = checkKindIsCoeffect s t

inferCoeffectTypeAssumption :: (?globals :: Globals)
                            => Span -> Assumption -> Checker (Maybe Type)
inferCoeffectTypeAssumption _ (Linear _) = return Nothing
inferCoeffectTypeAssumption s (Discharged _ c) = do
    t <- inferCoeffectType s c
    return $ Just t

checkKindIsCoeffect :: (?globals :: Globals) => Span -> Type -> Checker Type
checkKindIsCoeffect span ty = do
  kind <- inferKindOfType span ty
  case kind of
    KCoeffect -> return ty
    -- Came out as a promoted type, check that this is a coeffect
    KPromote k -> do
      kind' <- inferKindOfType span k
      case kind' of
        KCoeffect -> return ty
        _ -> throw KindMismatch{ errLoc = span, kExpected = KCoeffect, kActual = kind }

    _ -> throw KindMismatch{ errLoc = span, kExpected = KCoeffect, kActual = kind }

-- Find the most general unifier of two coeffects
-- This is an effectful operation which can update the coeffect-kind
-- contexts if a unification resolves a variable
mguCoeffectTypes :: (?globals :: Globals) => Span -> Coeffect -> Coeffect -> Checker Type
mguCoeffectTypes s c1 c2 = do
  ck1 <- inferCoeffectType s c1
  ck2 <- inferCoeffectType s c2
  case (ck1, ck2) of
    -- Both are variables
    (TyVar kv1, TyVar kv2) | kv1 /= kv2 -> do
      updateCoeffectType kv1 (KVar kv2)
      return (TyVar kv2)

    (t, t') | t == t' -> return t

   -- Linear-hand side is a poly variable, but right is concrete
    (TyVar kv1, ck2') -> do
      updateCoeffectType kv1 (promoteTypeToKind ck2')
      return ck2'

    -- Right-hand side is a poly variable, but Linear is concrete
    (ck1', TyVar kv2) -> do
      updateCoeffectType kv2 (promoteTypeToKind ck1')
      return ck1'

    (TyCon k1, TyCon k2) | k1 == k2 -> return $ TyCon k1

    -- Try to unify coeffect types
    (t, t') | Just tj <- joinCoeffectTypes t t' -> return tj

    -- Unifying a product of (t, t') with t yields (t, t') [and the symmetric version]
    (isProduct -> Just (t1, t2), t) | t1 == t -> return $ ck1
    (isProduct -> Just (t1, t2), t) | t2 == t -> return $ ck1
    (t, isProduct -> Just (t1, t2)) | t1 == t -> return $ ck2
    (t, isProduct -> Just (t1, t2)) | t2 == t -> return $ ck2

    (k1, k2) -> throw CoeffectUnificationError
      { errLoc = s, errTy1 = k1, errTy2 = k2, errC1 = c1, errC2 = c2 }

-- Given a coeffect type variable and a coeffect kind,
-- replace any occurence of that variable in an context
-- and update the current solver predicate as well
updateCoeffectType :: Id -> Kind -> Checker ()
updateCoeffectType tyVar k = do
   modify (\checkerState ->
    checkerState
     { tyVarContext = rewriteCtxt (tyVarContext checkerState),
       kVarContext = replace (kVarContext checkerState) tyVar k })
 where
   rewriteCtxt :: Ctxt (Kind, Quantifier) -> Ctxt (Kind, Quantifier)
   rewriteCtxt [] = []
   rewriteCtxt ((name, (KPromote (TyVar kindVar), q)) : ctxt)
    | tyVar == kindVar = (name, (k, q)) : rewriteCtxt ctxt
   rewriteCtxt ((name, (KVar kindVar, q)) : ctxt)
    | tyVar == kindVar = (name, (k, q)) : rewriteCtxt ctxt
   rewriteCtxt (x : ctxt) = x : rewriteCtxt ctxt
