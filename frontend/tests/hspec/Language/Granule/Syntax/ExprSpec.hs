module Language.Granule.Syntax.ExprSpec where

import Test.Hspec hiding (Spec)
import qualified Test.Hspec as Test

import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span

spec :: Test.Spec
spec = do
  describe "Expression helpers" $
    it "free variable test" $
      freeVars (Val nullSpanNoFile ()
            (Abs () (PVar nullSpanNoFile () $ mkId "x") Nothing
              (Val nullSpanNoFile ()
                (Abs () (PVar nullSpanNoFile () $ mkId "y") Nothing
                  (Val nullSpanNoFile () (Var () $ mkId "z")))))) `shouldBe` [mkId "z"]
