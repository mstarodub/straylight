module Tests where

import Data.Bifunctor
import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Numeric.Natural
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
import Test.QuickCheck.Arbitrary.Generic
import qualified Text.Regex as Regex

import Elab
import Order
import Superpos

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

strip_ansi :: String -> String
strip_ansi s = Regex.subRegex re s ""
  where
    -- taken from https://hackage.haskell.org/package/hledger-lib-1.34/docs/src/Hledger.Utils.String.html#stripAnsi
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
  [ ("forall (a:*) (b:*). a -> b -> c", Pi "a" (Sort Star) $ Pi "b" (Sort Star) $ Bound 1 :-> Bound 1 :-> Const "c")
  , ("a b c (d e) f", Const "a" :@ Const "b" :@ Const "c" :@ (Const "d" :@ Const "e") :@ Const "f")
  , ("λ x y z. z", ALam "x" (Sort Star) $ ALam "y" (Sort Star) $ ALam "z" (Sort Star) $ Bound 0)
  ]

-- church numeral reduction tests
data ArithTestExpr
  = AN Natural
  | ASucc ArithTestExpr
  | AAdd ArithTestExpr ArithTestExpr
  | AMul ArithTestExpr ArithTestExpr
  -- enabling exp in ghci leads to hangs
  --   | AExp ArithTestExpr ArithTestExpr
  deriving (Show, Eq, Ord, Generic)
  deriving (Arbitrary) via (GenericArbitrary ArithTestExpr)
instance Arbitrary Natural where
  arbitrary = elements [0 .. 2]
interp_arith_test :: ArithTestExpr -> Natural
-- interp_arith_test (AExp ae1 ae2) = interp_arith_test ae1 ^ interp_arith_test ae2
interp_arith_test (AN ae) = ae
interp_arith_test (ASucc ae) = succ $ interp_arith_test ae
interp_arith_test (AAdd ae1 ae2) = interp_arith_test ae1 + interp_arith_test ae2
interp_arith_test (AMul ae1 ae2) = interp_arith_test ae1 * interp_arith_test ae2
church_arith_test :: ArithTestExpr -> Term
-- church_arith_test (AExp ae1 ae2) = Const "exp" :@ church_arith_test ae1 :@ church_arith_test ae2
church_arith_test (AN nat) = church_nat nat
church_arith_test (ASucc ae) = Const "succ" :@ church_arith_test ae
church_arith_test (AAdd ae1 ae2) = Const "add" :@ church_arith_test ae1 :@ church_arith_test ae2
church_arith_test (AMul ae1 ae2) = Const "mul" :@ church_arith_test ae1 :@ church_arith_test ae2
church_nat :: Natural -> Term
church_nat i =
  runTC_partial $
    check
      nat_prelude
      (RLam "N" $ RLam "s" $ RLam "z" $ iterate (RVar "s" `RApp`) (RVar "z") `List.genericIndex` i)
      (get_const_def_partial nat_prelude "Nat")
nat_prelude :: ElabCtx
nat_prelude =
  input_str
    [ "let Nat  : * = forall N:*. (N -> N) -> N -> N;"
    , "let succ : Nat -> Nat = \\a N s z. s (a N s z);"
    , "let add  : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);"
    , "let mul  : Nat -> Nat -> Nat = \\a b N s z. a N (b N s) z;"
    , "let exp  : Nat -> Nat -> Nat = \\a b N. b (N -> N) (a N);"
    ]

green_test_ctx =
  input_str
    -- the types do not matter for this test
    [ "free 0 : *;"
    , "free 1 : *;"
    , "free 2 : *;"
    , "free 3 : *;"
    , "free 9 : ?0 -> ?1;"
    , "const f : ?0 -> ?1 -> ?2 -> ?3;"
    , "const g : ?0 -> ?1;"
    , "const a : *;"
    , "const b : *;"
    , "const ty : *;"
    , "const h : ?0 -> ?1 -> ?2;"
    , "const c : *;"
    ]
green_test_tm =
  Const "f"
    :@ (Const "g" :@ Const "a")
    :@ (Free 9 :@ Const "b")
    :@ ALam "x" (Const "ty") (Const "h" :@ Const "c" :@ (Const "g" :@ Bound 0))
green_test_val = eval green_test_ctx green_test_tm

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
  describe "elab reduction" do
    prop "random church num expression" $ \ae ->
      let num = interp_arith_test ae
      in within 1000000 $
          abe_conv nat_prelude (eval nat_prelude $ church_nat num) (eval nat_prelude $ church_arith_test ae)
  describe "core calculus" do
    it "green positions" do
      map fst (green_subtms green_test_val) `shouldBe` [[], [0], [0, 0], [1], [2]]
    it "green context replace" do
      quote green_test_ctx (green_replace [0, 0] (eval green_test_ctx $ Const "f" :@ Free 9) green_test_val)
        `shouldBe` Const "f"
          :@ (Const "g" :@ (Const "f" :@ Free 9))
          :@ (Free 9 :@ Const "b")
          :@ ALam "x" (Const "ty") (Const "h" :@ Const "c" :@ (Const "g" :@ Bound 0))

main :: IO ()
main = spec
