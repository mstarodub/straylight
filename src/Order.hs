module Order where

import Data.Map (Map)
import qualified Data.Map as Map (empty, insertWith, map, unionWith)
import Numeric.Natural

import Elab

-- the completeness of lambda-superposition depends on an order that is stable under substitutions,
-- however the derived Kbo from "superposition with lambdas" is not stable for eta-long terms (which is what we have sometimes).
-- (similar issues arise when finding green subterms later)
-- (the incompleteness resulting from ignoring this swould be minor [source: private communication with Blanchette],
-- because most terms that come up in practice are identical in their η-long and η-short forms).
-- there are two options for obtaining a reflexive closure of the nonground, strict term order ⪰_λ:
-- 1. s ≻_λ t ⟺ O(s) ≻_fo O(t), and use αβη-convertibility to obtain the reflexive closure
-- 2. equip ≻_fo with syntactic equality (deriving instance Eq FO(F)Val) to obtain ⪰_fo, then define: s ⪰_λ t ⟺ O(s) ⪰_fo O(t)
-- both options only work with η-normal values (long or short, they just have to both be either expanded or reduced).
-- the whole point is that η-equivalent higher-order terms should compare as equal under ⪰_λ.
-- (a third option would be to implement η-long NbE + an unpublished order from Blanchette, which does not exhibit the problem
-- of being unstable under η-long substitutions, and would actually make the calculus complete [source: private
-- communication with Bentkamp]

-- first-order values. flattened
data FOFTerm
  = FOFMeta Metavar
  | FOFRigid (Either Idx Name)
  | FOFApp FOFTerm FOFTerm
  | FOFSort Sorts
  deriving (Eq, Ord, Show)

type VarBal = Map Metavar Integer

ckbo :: Value -> Value -> Maybe Ordering
ckbo v1 v2 = o v1 `kbo` o v2

-- naive version
-- TODO: fluid
kbo :: FOFTerm -> FOFTerm -> Maybe Ordering
-- TODO: contains check + meta meta head
kbo (FOFMeta _) (FOFMeta _) = Nothing
kbo s t | s == t = Just EQ
kbo s t = do
  x <- varcheck
  y <- weight_test
  case x of
    EQ -> pure y
    _ -> if x == y then pure x else Nothing
  where
    (hs, ht) = (get_head s, get_head t)
    (ts, tt) = (get_tail s, get_tail t)
    -- only possibilities are Nothing / Just LT / Just GT
    weight_test :: Maybe Ordering
    weight_test =
      let
        a = ϕ s `compare` ϕ t
        b = hs `compare` ht
      in
        if a /= EQ
          then Just a
          else
            if b /= EQ
              then Just b
              else ts `ckbolex` tt
    -- n(x,s) ? n(x,t): variable balance
    varcheck :: Maybe Ordering
    varcheck =
      foldr cmp_f (Just EQ) $
        Map.unionWith (+) fs (Map.map negate ft)
    (fs, ft) = (free_occurencies s, free_occurencies t)
    cmp_f :: Integer -> Maybe Ordering -> Maybe Ordering
    cmp_f _ Nothing = Nothing
    cmp_f v (Just EQ) | v == 0 = Just EQ
    cmp_f v (Just EQ) | v < 0 = Just LT
    cmp_f v (Just EQ) | v > 0 = Just GT
    cmp_f v (Just LT) | v > 0 = Nothing
    cmp_f v (Just GT) | v < 0 = Nothing
    cmp_f _ (Just LT) = Just LT
    cmp_f _ (Just GT) = Just GT
    cmp_f _ _ = error "impossible"

-- if this returns Just EQ, then all subterms are syntactically equal.
-- because we already compared for syntactic equality prior to calling this
-- in kbo and took a different path there, we can thus assume this will only
-- return Nothing / Just LT / Just GT only
ckbolex :: [FOFTerm] -> [FOFTerm] -> Maybe Ordering
ckbolex [] [] = Just EQ
ckbolex (x : xs) (y : ys) =
  let res = kbo x y
  in if res == Just EQ then ckbolex xs ys else res
-- differently curried heads. impossible because number of args gets encoded into head
ckbolex _ _ = error "broken invariant"

-- TODO
get_head :: FOFTerm -> FOFTerm
get_head = undefined
get_tail :: FOFTerm -> [FOFTerm]
get_tail = undefined

free_occurencies :: FOFTerm -> VarBal
free_occurencies = go Map.empty
  where
    go mp (FOFMeta m) = Map.insertWith (+) m 1 mp
    go mp (FOFApp t1 t2) = go (go mp t1) t2
    go mp _ = mp

-- trivially admissible weight function.
-- an example heuristic could be: sorts > _lam > bound vars > _pi > consts
ϕ :: FOFTerm -> Natural
ϕ (FOFMeta _) = μ
ϕ (FOFSort _) = μ
ϕ (FOFRigid (Left _)) = μ
ϕ (FOFRigid (Right _)) = μ
ϕ (FOFApp t1 t2) = ϕ t1 + ϕ t2

μ :: Natural
μ = 1

-- encoding could be done lazily with get_args if we had a first-order representation
-- TODO: for now, only forced terms may be compared - is this what we want?
o :: Value -> FOFTerm
o = mk_fof . go . eta_reduce . quote_0_nonforcing
  where
    -- future improvement with η-long stable TO: here is how it could look like on values
    -- currently we can't do this because we need to eta reduce before encoding,
    -- which only seems to be possible on terms.
    -- this fn is similar to strip_abstr, abe_conv, quote
    -- important: the debruijn levels in these intermediate values are actually indices.
    -- go :: Lvl -> Value -> Value
    -- go l (VLam _ b) = olam `value_app` (go (l + 1) (b $ VBound l))
    -- go l (VPi _ a b) = opi `value_app` a `value_app` (go (l + 1) (b $ VBound l))
    -- go l (VFlex m sp) = VFlex m $ fmap (go (l + 1)) sp
    -- go l (VRigid (Left x) sp) = VRigid (Left . coerce $ lvl2idx l x) $ fmap (go (l + 1)) sp
    -- go l (VRigid (Right n) sp) = VRigid (Right n) $ fmap (go (l + 1)) sp
    -- go _ v = v
    -- TODO: this is insufficiently recursive
    go :: Term -> Term
    go (ALam _ a b) = olam :@ a :@ b
    go (Pi _ a b) = opi :@ a :@ b
    go (t1 :@ t2) = go t1 :@ go t2
    go t = t
    olam = Const "_lam"
    opi = Const "_pi"
    mk_fof :: Term -> FOFTerm
    mk_fof (Free m) = FOFMeta m
    mk_fof (Bound i) = FOFRigid (Left i)
    mk_fof (Const s) = FOFRigid (Right s)
    mk_fof (Sort k) = FOFSort k
    mk_fof (t1 :@ t2) = mk_fof t1 `FOFApp` mk_fof t2
    mk_fof _ = error "broken invariant"

-- TODO: optimized, single traversal
tkbo :: VarBal -> Integer -> FOFTerm -> FOFTerm -> (VarBal, Integer, Maybe Ordering)
-- tkbo vb wb (FOFMeta x) (FOFMeta y) = (inc_vb x $ dec_vb y vb, wb, if x == y then Just EQ else Nothing)
tkbo _ _ _ _ = undefined

inc_vb, dec_vb :: Metavar -> VarBal -> VarBal
inc_vb m = Map.insertWith (+) m 1
dec_vb m = Map.insertWith (+) m -1
