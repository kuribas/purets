{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Test.Hspec
import Language.Ast
import Language.TypeCheck
import Control.Unification (UTerm(..))
import qualified Data.Map as Map
import qualified Data.Text as Text

mkName :: Text.Text -> Name
mkName x = Name x 0

mkTypeVar :: Text.Text -> TypeTerm
mkTypeVar x = UTerm $ TypeVar (mkName x) KindType

forall_ :: [Text.Text] -> (Type TypeTerm) -> TypeTerm
forall_ vars tp = UTerm $ TypeForall (map mkName vars) tp


a, b, c, f, g :: TypeTerm
a = mkTypeVar "a"
b = mkTypeVar "b"
c = mkTypeVar "c"
f = mkTypeVar "f"
g = mkTypeVar "g"

stringType :: TypeTerm
stringType = UTerm $ TypeCon (Name "string" 0) []

initTypes :: VarTypeMap
initTypes = Map.fromList
  [ (Name "inc" 0, UTerm $ TypeArr intType intType)
  , (Name "id" 0, forall_ ["a"] $ TypeArr a a)
  , (Name "const" 0, forall_ ["a", "b"] $ TypeArr a $ UTerm $ TypeArr b a)
  , (Name "plus" 0, UTerm $ TypeArr intType $ UTerm $ TypeArr intType intType)
  ]

inc, id_ :: Expr (Maybe TypeTerm)
inc = Var Nothing $ mkName "inc"
id_ = Var Nothing $ mkName "id"
const_ = Var Nothing $ mkName "const"
plus = Var Nothing $ mkName "plus"

initEnv = InferEnv {varTypes = initTypes, typeMap = Map.empty}  

-- 5
expr1 :: Expr (Maybe TypeTerm)
expr1 = Lit Nothing $ LInt 5

-- (5 :: Int) :: float
expr2 :: Expr (Maybe TypeTerm)
expr2 = Ascr (Just floatType) $ Lit Nothing $ LInt 5

-- inc 4
expr3 :: Expr (Maybe TypeTerm)
expr3 = App Nothing inc (Lit Nothing (LInt 4))

-- (4 :: Int) + (4.0 :: Float)
expr4 :: Expr (Maybe TypeTerm)
expr4 = App Nothing
        (App Nothing plus (Lit Nothing (LInt 4)))
        (Lit Nothing (LFloat 4))

-- (a -> a) :: (a -> b)
expr5 :: Expr (Maybe TypeTerm)
expr5 = App (Just $ forall_ ["b", "a"] $ TypeArr b a) id_
        (Lit Nothing (LInt 4))

-- (const 4) :: Int
expr6 :: Expr (Maybe TypeTerm)
expr6 = App (Just intType) const_ (Lit Nothing (LInt 4))


main :: IO ()
main = hspec spec

spec :: Spec
spec = _
  -- describe "parse XML tests" $ do
  -- it "skips tags" $
  --   parseXMLByteString (tag "foo" skipAttrs $ const skipTags)
  --   (ParseOptions Nothing Nothing) "<foo></foo>"
  --   `shouldBe` (Right () :: Either (EventParseError String, Maybe XMLParseLocation) ())

  
