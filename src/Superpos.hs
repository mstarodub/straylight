{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Superpos where

import Data.Foldable
import qualified Data.List as List
import Data.Maybe
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Seq
import Numeric.Natural

import Elab
import Order

data Literal' a = Pos (a, a) | Neg (a, a)
  deriving (Functor)
lfst (Pos (x, _)) = x
lfst (Neg (x, _)) = x
lsnd (Pos (_, y)) = y
lsnd (Neg (_, y)) = y
type Literal = Literal' Value
pattern a :≉ b = Neg (a, b)
pattern a :≈ b = Pos (a, b)
infix 4 :≉
infix 4 :≈

-- unoriented equality for literals
eq_lit :: Substitution -> Literal -> Literal -> Bool
eq_lit sig l r = case (l, r) of
  (Pos l', Pos r') -> go l' r'
  (Neg l', Neg r') -> go l' r'
  (_, _) -> False
  where
    (c1, c2) `go` (d1, d2) = c1 `cmp` d1 && c2 `cmp` d2 || c1 `cmp` d2 && c2 `cmp` d1
    cmp = abe_conv sig

show_lit :: ElabCtx -> Literal -> String
show_lit ctx (Pos (l, r)) = show_val ctx l <> "≈" <> show_val ctx r
show_lit ctx (Neg (l, r)) = show_val ctx l <> "≉" <> show_val ctx r

-- plain lists are fine here, since clause sets are commonly not large
-- duplicates should be deleted
newtype Clause = Cl [Literal]

map_clause :: (Literal -> Literal) -> Clause -> Clause
map_clause f (Cl cl) = Cl $ f `map` cl

show_cl :: ElabCtx -> Clause -> String
show_cl _ (Cl []) = "⊥"
show_cl ctx (Cl cs) = List.intercalate " ∨ " (show_lit ctx <$> cs)

-- we use plain lists for now, although it's quite inefficient
type Formset = [Clause]

bool_prelude :: ElabCtx
bool_prelude =
  input_str
    [ "const Bool : *;"
    , "free 0 : *;" -- a
    , "free 1 : Bool;" -- x : Bool
    , "free 2 : Bool;" -- y : Bool
    , "free 3 : ?0;" -- x : a
    , "free 4 : ?0;" -- y : a
    , "free 5 : ?0 -> Bool;" -- y : a -> Bool
    , "const t : Bool;"
    , "const f : Bool;"
    , "const not : Bool -> Bool;"
    , "const and : Bool -> Bool -> Bool;"
    , "const or : Bool -> Bool -> Bool;"
    , "const impl : Bool -> Bool -> Bool;"
    , "const equiv : Bool -> Bool -> Bool;"
    , "const ∀ : forall a:*. (a -> Bool) -> Bool;"
    , "const ∃ : forall a:*. (a -> Bool) -> Bool;"
    , "const eq : forall a:*. a -> a -> Bool;"
    , "const hchoice : forall a:*. (a -> Bool) -> a;"
    ]

-- TODO: how do we add these into the prover state?
bool_axioms :: Formset
bool_axioms =
  [ Cl [t_ :≉ f_]
  , Cl [x_ :≈ t_, x_ :≈ f_]
  , Cl [not_ `va` t_ :≈ f_]
  , Cl [not_ `va` f_ :≈ t_]
  , Cl [and_ `va` t_ `va` x_ :≈ x_]
  , Cl [and_ `va` f_ `va` x_ :≈ f_]
  , Cl [or_ `va` t_ `va` x_ :≈ t_]
  , Cl [or_ `va` f_ `va` x_ :≈ x_]
  , Cl [impl_ `va` t_ `va` x_ :≈ x_]
  , Cl [impl_ `va` f_ `va` x_ :≈ t_]
  , Cl [xa_ :≉ ya_, eq_ `va` a_ `va` xa_ `va` ya_ :≈ t_]
  , Cl [xa_ :≈ ya_, eq_ `va` a_ `va` xa_ `va` ya_ :≈ f_]
  , Cl [equiv_ `va` x_ `va` y_ :≈ and_ `va` (impl_ `va` x_ `va` y_) `va` (impl_ `va` y_ `va` x_)]
  , Cl [forall_ `va` a_ `va` (VLam "x" a_ $ \_ -> t_) :≈ t_]
  , Cl [yatobool_ :≈ (VLam "x" a_ $ \_ -> t_), forall_ `va` a_ `va` yatobool_ :≈ f_]
  , Cl [exists_ `va` a_ `va` yatobool_ :≈ not_ `va` (forall_ `va` a_ `va` (VLam "x" a_ $ \x -> not_ `va` (yatobool_ `va` x)))]
  , Cl [yatobool_ `va` xa_ :≈ f_, yatobool_ `va` (hchoice_ `va` a_ `va` yatobool_) :≈ t_]
  ]
  where
    [a_, x_, y_, xa_, ya_, yatobool_] = get_free_def_partial bool_prelude `map` [0 .. 5]
    [t_, f_, not_, and_, or_, impl_, equiv_, forall_, exists_, eq_, hchoice_] =
      get_const_def_partial bool_prelude `map` ["t", "f", "not", "and", "or", "impl", "equiv", "∀", "∃", "eq", "hchoice"]
    va = value_app bool_prelude.metactx

base_prelude :: ElabCtx
base_prelude =
  append_input_str
    bool_prelude
    [ "const funext : forall (a:*) (b:*). (a -> b) -> (a -> b) -> a;"
    , "free 6 : *;" -- a
    , "free 7 : *;" -- b
    , "free 8 : ?6 -> ?7;" -- y
    , "free 9 : ?6 -> ?7;" -- z
    ]

ext_ax :: Clause
ext_ax =
  Cl
    [ y_ `va` (funext_ `va` a_ `va` b_ `va` y_ `va` z_) :≉ z_ `va` (funext_ `va` a_ `va` b_ `va` y_ `va` z_)
    , y_ :≈ z_
    ]
  where
    [a_, b_, y_, z_] = get_free_def_partial base_prelude `map` [6 .. 9]
    funext_ = get_const_def_partial base_prelude "funext"
    va = value_app base_prelude.metactx

-- different convention compared to the paper. we start at 0 and the list is reversed
type Position = [Natural]

-- TODO: this is likely very incorrect. the calculus assumes η-short nf everywhere, and
--   this won't recurse under η-contractible lambdas. perhaps we can solve it with
--   quote -> eta_reduce -> eval?
-- TODO: we don't force here. the forcing (and passing of ctx) is getting out of hand -
--   we need to decide precisely where in the pipeline values need to be forced
--   places to check: comparison (order), ...
green_subtms :: Value -> [(Position, Value)]
green_subtms = go []
  where
    go :: Position -> Value -> [(Position, Value)]
    go posacc v = (posacc, v) : rest
      where
        rest :: [(Position, Value)]
        rest = case v of
          -- we never recurse under a lambda, so no bound vars
          VRigid (Right _) sp _ -> concat $ zipWith go ((: posacc) `map` [0 ..]) $ toList sp
          _ -> []

green_replace :: Position -> Value -> Value -> Value
green_replace [] by _ = by
green_replace (p : ps) by (VRigid (Right s) sp a) = VRigid (Right s) sp' a
  where
    sp' = Seq.update (fromIntegral p) (green_replace ps by (fromJust $ Seq.lookup (fromIntegral p) sp)) sp
green_replace _ _ _ = error "broken invariant"

-- same overapproximation as in the term order
is_fluid_val :: Value -> Bool
is_fluid_val (VFlex _ _ _) = True
is_fluid_val (VLam _ _ b) = has_val_freevars (b dummy_conv_val_unsafe)
  where
    -- TODO: again, the nested types of lambdas found in the body are also scanned. is that correct?
    has_val_freevars :: Value -> Bool
    has_val_freevars (VFlex _ _ _) = True
    has_val_freevars (VRigid _ sp _) = any has_val_freevars sp
    has_val_freevars (VLam _ a bty) = has_val_freevars a || has_val_freevars (bty dummy_conv_val_unsafe)
    has_val_freevars (VPi _ a bty) = has_val_freevars a || has_val_freevars (bty dummy_conv_val_unsafe)
    has_val_freevars (VSort _) = False
is_fluid_val _ = False

-- TODO: explain this
cmp_lits :: Literal -> Literal -> PartialOrd
cmp_lits lit1 lit2 = do
  l1l2 <- ckbo (lfst lit1) (lfst lit2)
  l1r2 <- ckbo (lfst lit1) (lsnd lit2)
  r1l2 <- ckbo (lsnd lit1) (lfst lit2)
  r1r2 <- ckbo (lsnd lit1) (lsnd lit2)
  pure $ case (l1l2, l1r2, r1l2, r1r2, sign lit1 lit2) of
    (GT, GT, _, _, _) -> GT
    (_, _, GT, GT, _) -> GT
    (LT, _, LT, _, _) -> LT
    (_, LT, _, LT, _) -> LT
    (GT, _, _, GT, _) -> GT
    (LT, _, _, LT, _) -> LT
    (_, GT, GT, _, _) -> GT
    (_, LT, LT, _, _) -> LT
    (EQ, _, _, c, EQ) -> c
    (_, EQ, c, _, EQ) -> c
    (_, c, EQ, _, EQ) -> c
    (c, _, _, EQ, EQ) -> c
    (EQ, _, _, EQ, _) -> EQ
    (_, EQ, EQ, _, _) -> EQ
    (EQ, _, _, _, c) -> c
    (_, EQ, _, _, c) -> c
    (_, _, EQ, _, c) -> c
    (_, _, _, EQ, c) -> c
  where
    sign (Pos _) (Pos _) = EQ
    sign (Neg _) (Neg _) = EQ
    sign (Neg _) (Pos _) = GT
    sign (Pos _) (Neg _) = LT

-- TODO: sig ≡ id ⟹ "we leave it implicit"?
-- our clauses are deduplicated, but maximal ⇏ strictly maximal because there might be more than
-- one element equal according to the order
-- TODO: example / when is this the case?
eligible :: Bool -> Literal -> Substitution -> Clause -> Bool
eligible strictly l sig cl = all maximal clcompared
  where
    maximal = flip (elem @[]) $ [Just GT, Nothing] <> if strictly then [] else [Just EQ]
    clcompared = cmp_lits lsig `map` clsig
    Cl clsig = map_clause (fmap $ apply_subst sig) cl
    lsig = apply_subst sig <$> l

occurs_deeply :: ElabCtx -> Metavar -> Clause -> Bool
occurs_deeply ctx m (Cl cl) = any go cl
  where
    go :: Literal -> Bool
    go l =
      occ_lam False (quote ctx $ lfst l)
        || occ_lam False (quote ctx $ lsnd l)
        || occ_free False (lfst l)
        || occ_free False (lsnd l)
    -- TODO: dependent types
    occ_lam :: Bool -> Term -> Bool
    occ_lam True (Free n) = m == n
    occ_lam _ (ALam _ _ t) = occ_lam True t
    occ_lam deep (t1 :@ t2) = occ_lam deep t1 || occ_lam deep t2
    occ_lam _ _ = False
    occ_free :: Bool -> Value -> Bool
    occ_free True (VFree n _) = m == n
    occ_free deep (VRigid _ sp _) = any (occ_free deep) sp
    occ_free _ (VFlex _ sp _) = any (occ_free True) sp
    occ_free _ _ = False
