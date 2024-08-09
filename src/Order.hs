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
  deriving (Eq, Show)
pattern FOFConst x = FOFRigid (Right x)
pattern FOFBound i = FOFRigid (Left i)

-- kbo precedence given by default Ord
deriving instance Ord FOFTerm

type PartialOrd = Maybe Ordering

ckbo :: Value -> Value -> PartialOrd
ckbo v1 v2 = encode v1 `kbo` encode v2

-- naive version
-- TODO: fluid
kbo :: FOFTerm -> FOFTerm -> PartialOrd
-- TODO: contains check + meta meta head
kbo (FOFMeta _) (FOFMeta _) = Nothing
kbo s t | s == t = Just EQ
kbo s t = do
  x <- varcheck s t
  y <- weight_test s t
  case x of
    EQ -> pure y
    _ -> if x == y then pure x else Nothing

-- if this returns Just EQ, then all subterms are syntactically equal.
-- because we already compared for syntactic equality prior to calling this
-- in kbo and took a different path there, we can thus assume this will only
-- return Nothing / Just LT / Just GT only
ckbolex :: [FOFTerm] -> [FOFTerm] -> PartialOrd
ckbolex [] [] = Just EQ
ckbolex (x : xs) (y : ys) =
  let res = kbo x y
  in if res == Just EQ then ckbolex xs ys else res
-- differently curried heads. impossible, since number of args gets encoded into the head
ckbolex _ _ = error "broken invariant"

-- only possibilities are Nothing / Just LT / Just GT
weight_test :: FOFTerm -> FOFTerm -> PartialOrd
weight_test s t =
  if a /= EQ
    then Just a
    else
      if b /= EQ
        then Just b
        else ts `ckbolex` tt
  where
    (hs, ht) = (get_fof_head s, get_fof_head t)
    (ts, tt) = (get_fof_tail s, get_fof_tail t)
    a = ϕ s `compare` ϕ t
    b = hs `compare` ht

type VarBal = Map Metavar Integer

-- n(x,s) ? n(x,t): variable balance
varcheck :: FOFTerm -> FOFTerm -> PartialOrd
varcheck s t = foldr cmp_f (Just EQ) $ Map.unionWith (+) fs (Map.map negate ft)
  where
    (fs, ft) = (free_occurencies s, free_occurencies t)
    cmp_f :: Integer -> PartialOrd -> PartialOrd
    cmp_f _ Nothing = Nothing
    cmp_f v (Just EQ) | v == 0 = Just EQ
    cmp_f v (Just EQ) | v < 0 = Just LT
    cmp_f v (Just EQ) | v > 0 = Just GT
    cmp_f v (Just LT) | v > 0 = Nothing
    cmp_f v (Just GT) | v < 0 = Nothing
    cmp_f _ (Just LT) = Just LT
    cmp_f _ (Just GT) = Just GT
    cmp_f _ _ = error "impossible"
    free_occurencies :: FOFTerm -> VarBal
    free_occurencies = go Map.empty
      where
        go mp (FOFMeta m) = Map.insertWith (+) m 1 mp
        go mp (FOFApp t1 t2) = go (go mp t1) t2
        go mp _ = mp

get_fof_head :: FOFTerm -> FOFTerm
get_fof_head (FOFApp t1 _) = get_fof_head t1
get_fof_head t = t

get_fof_tail :: FOFTerm -> [FOFTerm]
get_fof_tail (FOFApp t1 t2) = get_fof_tail t1 <> [t2]
get_fof_tail _ = []

-- trivially admissible weight function.
-- an example heuristic could be: sorts > _lam > bound vars > _pi > consts
ϕ :: FOFTerm -> Natural
ϕ t = case t of
  FOFMeta _ -> μ
  FOFSort _ -> μ
  FOFRigid (Left _) -> μ
  FOFRigid (Right _) -> μ
  FOFApp t1 t2 -> ϕ t1 + ϕ t2
  where
    μ :: Natural
    μ = 1

-- encoding could be done lazily with get_args if we had a first-order representation
-- TODO: for now, only forced terms may be compared - is this what we want?
-- TODO: forcing should be possible to do during quoting "for free". also forcing up to head is not enough?
encode :: Value -> FOFTerm
encode = o . eta_reduce . quote_0_nonforcing

o :: Term -> FOFTerm
o = mk_fof 0 . go
  where
    go :: Term -> Term
    go (ALam _ a b) = olam :@ go a :@ go b
    go (Pi _ a b) = opi :@ go a :@ go b
    go (t1 :@ t2) = go t1 :@ go t2
    go t = t
    olam = Const "_lam"
    opi = Const "_pi"
    mk_fof :: Natural -> Term -> FOFTerm
    mk_fof _ (Free m) = FOFMeta m
    mk_fof _ (Bound i) = FOFRigid (Left i)
    mk_fof _ (Sort k) = FOFSort k
    mk_fof d (Const s) = FOFRigid (Right $ odepth d s)
    mk_fof d (t1 :@ t2) = mk_fof (d + 1) t1 `FOFApp` mk_fof 0 t2
    mk_fof _ _ = error "broken invariant"
    -- encode the number of arguments
    odepth d (Name s) = Name $ s <> "_" <> show d

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

-- TODO: optimized, single traversal
tkbo :: VarBal -> Integer -> FOFTerm -> FOFTerm -> (VarBal, Integer, PartialOrd)
-- tkbo vb wb (FOFMeta x) (FOFMeta y) = (inc_vb x $ dec_vb y vb, wb, if x == y then Just EQ else Nothing)
tkbo _ _ _ _ = undefined

inc_vb, dec_vb :: Metavar -> VarBal -> VarBal
inc_vb m = Map.insertWith (+) m 1
dec_vb m = Map.insertWith (+) m -1
