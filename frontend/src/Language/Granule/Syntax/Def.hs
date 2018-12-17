{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}

module Language.Granule.Syntax.Def where

import Data.List ((\\), delete)
import GHC.Generics (Generic)

import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Pattern

-- | Top-level ASTs
-- | Comprise a list of data type declarations and a list
-- | of expression definitions
-- | where `v` is the type of values and `a` annotations
data AST v a = AST [DataDecl] [Def v a]


deriving instance (Show (Value v a), Show a) => Show (AST v a)
deriving instance Functor (AST v)

-- | Expression definitions
data Def v a = Def Span Id (Expr v a) [Pattern a] TypeScheme
  deriving Generic


magic :: AST () () -> AST () ()
magic (AST dd dfs) = AST dd (map foo dfs)
  where
    foo :: Def () () -> Def () ()
    foo (Def sp nm bdy  pats  (Forall spT binders ty)) =
        (Def sp nm bdy' pats' (Forall spT binders ty'))
      where
        pats' = map patToBox pats
          where
            patToBox = \case
              PBox sp () p -> PBox sp () (patToBox p)
              PConstr sp () nm ps -> PBox sp () $ PConstr sp () nm (map patToBox ps)
              p -> PBox (getSpan p) () p

        ty' = der ty
          where
            der = \case
              FunTy (Box c t1) t2 -> FunTy (Box c (der t1)) (der t2)
              FunTy t1 t2 -> FunTy (Box (COne (TyCon $ mkId "Nat")) (der t1)) (der t2)
              Box c t -> Box c (der t)
              TyApp t1 (Box c t2) -> TyApp (der t1) (Box c $ der t2)
              TyApp t1 t2 -> TyApp (der t1) (Box (COne (TyCon $ mkId "Nat")) (der t2))
              t -> t -- sloppy, I know

        bdy' = promBody $ promArg bdy
          where
            promArg = \case
              App sp _ e1 e2 -> App sp () (promArg e1) (Val nullSpan () $ Promote () (promArg e2))
              Binop sp _ op e1 e2 -> Binop sp () op (promArg e1) (promArg e2)
              -- LetDiamond sp _ p ty e1 e2 ->  LetDiamond sp () p ty (promArg e1) (promArg e2)
              Val sp _ v -> Val sp () $ case v of
                Promote _ e -> Promote () (promArg e)
                Pure _ e -> undefined
                Abs _ p ty e -> Abs () p ty (promArg e)
                v -> v
              Case sp _ eScrut branches -> Case sp () (promArg eScrut) (map (\(p,e) -> (p,promArg e)) branches)

            promBody e = case returnTy ty of
              Box{} -> Val nullSpan () $ Promote () e
              _ -> e
              where
                returnTy = \case
                  FunTy _ t2 -> returnTy t2
                  t -> t

deriving instance Functor (Def v)
deriving instance (Show (Value v a), Show a) => Show (Def v a)
instance FirstParameter (Def v a) Span

-- | Data type declarations
data DataDecl = DataDecl Span Id [(Id,Kind)] (Maybe Kind) [DataConstr]
  deriving (Generic, Show)

instance FirstParameter DataDecl Span

-- | Data constructors
data DataConstr
  = DataConstrG Span Id TypeScheme -- ^ GADTs
  | DataConstrA Span Id [Type]     -- ^ ADTs
  deriving (Eq, Show, Generic)

instance FirstParameter DataConstr Span


-- | How many data constructors a type has (Nothing -> don't know)
type Cardinality = Maybe Nat

-- | Fresh a whole AST
freshenAST :: AST v a -> AST v a
freshenAST (AST dds defs) = AST dds (map runFreshener defs)

{-| Alpha-convert all bound variables of a definition, modulo the things on the lhs
Eg this:
@
foo : Int -> Int
foo x = (\(x : Int) -> x * 2) x
@
will become
@
foo : Int -> Int
foo x = (\(x0 : Int) -> x0 * 2) x
@

>>> runFreshener $ Def ((1,1),(2,29)) (Id "foo" "foo") (App ((2,10),(2,29)) () (Val ((2,10),(2,25)) () (Abs () (PVar ((2,12),(2,12)) () (Id "x" "x0")) (Just (TyCon (Id "Int" "Int"))) (Binop ((2,25),(2,25)) () "*" (Val ((2,24),(2,24)) () (Var () (Id "x" "x0"))) (Val ((2,26),(2,26)) () (NumInt () 2))))) (Val ((2,29),(2,29)) () (Var () (Id "x" "x")))) [PVar ((2,5),(2,5)) () (Id "x" "x")] (Forall ((0,0),(0,0)) [] (FunTy (TyCon (Id "Int" "Int")) (TyCon (Id "Int" "Int"))))
Def ((1,1),(2,29)) (Id "foo" "foo") (App ((2,10),(2,29)) () (Val ((2,10),(2,25)) () (Abs () (PVar ((2,12),(2,12)) () (Id "x" "x_1")) (Just (TyCon (Id "Int" "Int"))) (Binop ((2,25),(2,25)) () "*" (Val ((2,24),(2,24)) () (Var () (Id "x" "x_1"))) (Val ((2,26),(2,26)) () (NumInt () 2))))) (Val ((2,29),(2,29)) () (Var () (Id "x" "x_0")))) [PVar ((2,5),(2,5)) () (Id "x" "x_0")] (Forall ((0,0),(0,0)) [] (FunTy (TyCon (Id "Int" "Int")) (TyCon (Id "Int" "Int"))))
-}
instance Freshenable (Def v a) where
  freshen (Def s var e ps t) = do
    ps <- mapM freshen ps
    t  <- freshen t
    e  <- freshen e
    return (Def s var e ps t)

instance Term (Def v a) where
  freeVars (Def _ name body binders _) = delete name (freeVars body \\ concatMap boundVars binders)
