module Tests where

import Data.Bifunctor
import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set
import Test.Hspec
import Test.QuickCheck
import Text.Megaparsec (SourcePos, initialPos)
import qualified Text.Regex as Regex

-- import Test.QuickCheck.Arbitrary.Generic
-- import GHC.Generics (Generic)
-- import Test.Hspec.QuickCheck

import Elab
import Order

instance Arbitrary Name where
  arbitrary = Name . List.singleton <$> elements ['w' .. 'z']
instance Arbitrary Metavar where
  arbitrary = Metavar <$> elements [0 .. 4]
instance Arbitrary SourcePos where
  arbitrary = pure $ initialPos mempty

-- deriving instance Generic Raw
-- deriving via (GenericArbitrary Raw) instance (Arbitrary Raw)

-- inefficient. should use smallcheck (enumerative pbt)
-- usage example: gen_setof_x @WTTerm 5
gen_setof_x :: (Arbitrary a, Ord a, Num b, Eq b) => b -> IO (Set a)
gen_setof_x = go Set.empty
  where
    go set 0 = pure set
    go set k = do
      term <- generate arbitrary
      if term `Set.member` set
        then go set k
        else go (Set.insert term set) (k - 1)

-- TODO: well-typed terms with types constructed from a set of base types
newtype WTTerm = WT Term
  deriving (Show, Eq) via Term
instance Arbitrary WTTerm where
  -- WT <$> arbitrary `suchThat` (isRight . infer_noctx [])
  arbitrary = do
    let basetypes :: [(Name, Value)] = [("Bool", VSort Star), ("Nat", VSort Star)]
    let _ctx = foldl define_const empty_ctx basetypes
    pure undefined

strip_ansi :: String -> String
strip_ansi s = Regex.subRegex re s ""
  where
    re = Regex.mkRegex "\ESC\\[([0-9]+;)*([0-9]+)?[ABCDHJKfmsu]"

getenc_headtail_test :: [((FOFTerm, [FOFTerm]), Term)]
getenc_headtail_test =
  [ ((FOFConst "a_2", [FOFConst "b_0", FOFConst "c_0"]), Const "a" :@ Const "b" :@ Const "c")
  , ((FOFConst "a_1", [FOFConst "b_1" `FOFApp` FOFConst "c_0"]), Const "a" :@ (Const "b" :@ Const "c"))
  , ((FOFConst "a_0", []), Const "a")
  , ((FOFConst "a_1", [FOFConst "b_0"]), Const "a" :@ Const "b")
  , ((FOFConst "a_2", [FOFConst "b_0", FOFConst "c_1" `FOFApp` FOFConst "d_0"]), Const "a" :@ Const "b" :@ (Const "c" :@ Const "d"))
  , ((FOFConst "a_2", [FOFConst "b_0", FOFConst "c_1" `FOFApp` FOFConst "d_0"]), (Const "a" :@ Const "b") :@ (Const "c" :@ Const "d"))
  , ((FOFConst "a_2", [FOFConst "c_1" `FOFApp` FOFConst "d_0", FOFConst "b_1" `FOFApp` (FOFConst "bb_1" `FOFApp` FOFConst "bbb_0")]), Const "a" :@ (Const "c" :@ Const "d") :@ (Const "b" :@ (Const "bb" :@ Const "bbb")))
  ]

pp_term_test :: [(String, Term)]
pp_term_test =
  [ ("forall a:* b:*. a -> b -> c", Pi "a" (Sort Star) $ Pi "b" (Sort Star) $ Bound 1 :-> Bound 1 :-> Const "c")
  , ("a b c (d e) f", Const "a" :@ Const "b" :@ Const "c" :@ (Const "d" :@ Const "e") :@ Const "f")
  , ("λ x y z. z", ALam "x" (Sort Star) $ ALam "y" (Sort Star) $ ALam "z" (Sort Star) $ Bound 0)
  ]

spec :: IO ()
spec = hspec do
  describe "kbo" do
    it "encoding"
      $ mapM_
        ( \((expected_hd, expected_tl), tval) -> do
            get_fof_head tval `shouldBe` expected_hd
            get_fof_tail tval `shouldBe` expected_tl
        )
      $ fmap (second o) getenc_headtail_test
    it "var condition" do
      let constr :: [Metavar] -> FOFTerm = foldl1 FOFApp . fmap FOFMeta
      varcheck (constr [0, 0, 1]) (constr [0, 1]) `shouldBe` Just GT
      varcheck (constr [0, 0, 1]) (constr [0, 1, 1]) `shouldBe` Nothing
      varcheck (constr [0, 0, 1]) (constr [0, 1, 2]) `shouldBe` Nothing
  describe "pretty printer" do
    it "term" $
      mapM_ (\(expected, tval) -> strip_ansi (show tval) `shouldBe` expected) pp_term_test

-- temporary helper to examine differences between functions on terms
-- newtype DiffTerm = DiffTerm Term
--   deriving (Show, Eq) via Term
-- instance Arbitrary DiffTerm where
--   arbitrary = do
--     let onwt (WT wt) = not $ alpha_eq [] (nf [] wt) (hnf [] wt)
--     (WT wt) <- arbitrary @WTTerm `suchThat` onwt
--     pure $ DiffTerm wt
