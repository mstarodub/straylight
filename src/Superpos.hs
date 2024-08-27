{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Superpos where

import Data.Foldable
import qualified Data.List as List
import Data.Maybe
import qualified Data.Sequence as Seq
import Numeric.Natural

import Core
import Elab
import Order
import Unif

pattern a :≉ b = Neg (a, b)
pattern a :≈ b = Pos (a, b)
infix 4 :≉
infix 4 :≈
{-# COMPLETE (:≉), (:≈) #-}

-- unoriented equality for literals
eq_lit :: Substitution -> Literal Value -> Literal Value -> Bool
eq_lit sig l r = case (l, r) of
  (Pos l', Pos r') -> go l' r'
  (Neg l', Neg r') -> go l' r'
  (_, _) -> False
  where
    (c1, c2) `go` (d1, d2) = c1 `cmp` d1 && c2 `cmp` d2 || c1 `cmp` d2 && c2 `cmp` d1
    cmp = abe_conv sig

show_lit :: ElabCtx -> Literal Value -> String
show_lit ctx (Pos (l, r)) = show_val ctx l <> " ≈ " <> show_val ctx r
show_lit ctx (Neg (l, r)) = show_val ctx l <> " ≉ " <> show_val ctx r

map_clause :: (Literal Value -> Literal Value) -> Clause -> Clause
map_clause f (Cl cl) = Cl $ f `map` cl

show_cl :: ElabCtx -> Clause -> String
show_cl _ (Cl []) = "⊥"
show_cl ctx (Cl cs) = List.intercalate " ∨ " (show_lit ctx <$> cs)

show_formset :: ElabCtx -> Formset -> String
show_formset ctx = List.intercalate " ∧ " . fmap (show_cl ctx)

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
is_fluid_val (VFlex _ sp _) = not $ Seq.null sp
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

-- TODO: sig ≡ id ⟹ "we leave it implicit"?
-- our clauses are deduplicated, but maximal ⇏ strictly maximal because there might be more than
-- one element equal according to the order
-- TODO: example / when is this the case?
-- precondition: substitution already applied (lsig)
eligible :: Bool -> Literal Value -> Substitution -> Clause -> Bool
eligible strictly lsig sig cl = all maximal clcompared
  where
    maximal = flip (elem @[]) $ [Just GT, Nothing] <> if strictly then [] else [Just EQ]
    clcompared = cmp_lits lsig `map` clsig
    Cl clsig = subst_clause sig cl

subst_clause :: Substitution -> Clause -> Clause
subst_clause sig cl = map_clause (fmap $ apply_subst sig) cl

occurs_deeply :: ElabCtx -> Metavar -> Clause -> Bool
occurs_deeply ctx m (Cl cl) = any go cl
  where
    go :: Literal Value -> Bool
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

-- simplified, complete condition (3). source: priv. comm. with Bentkamp
varcond :: Value -> Value -> Value -> Bool
-- tσ is a λ-abstraction
varcond (VFree _ _) tsig _ | VLam _ _ _ <- tsig = True
-- OR t'σ is a λ-abstraction
varcond (VFree _ _) _ t'sig | VLam _ _ _ <- t'sig = True
-- OR u is not a variable
varcond (VFree _ _) _ _ = False
varcond _ _ _ = True

-- TODO: not sure yet how to handle the csu computation, need to understand main loop first
csu_select :: Stream Substitution -> Substitution
csu_select = head . toList

-- TODO: partial, does not handle dependent types (the original calculus does not have them)
--   likely needs an infinite stream of possible ty t' results in the pi case
fluid_head_ty :: Value -> Value -> Value
fluid_head_ty u t' = VPi "" (non_pi_ty t') (ty u)
  where
    non_pi_ty :: Value -> Value
    non_pi_ty (VFlex _ _ a) = a
    non_pi_ty (VRigid _ _ a) = a
    non_pi_ty (VLam _ a _) = a
    non_pi_ty (VPi _ _ _) = error "TODO"
    non_pi_ty (VSort Star) = VSort Box
    non_pi_ty (VSort Box) = error "broken invariant"
    ty :: Value -> Value -> Value
    ty (VFlex _ _ a) = const a
    ty (VRigid _ _ a) = const a
    ty (VLam _ a _) = const a
    ty (VPi _ _ b) = b
    ty (VSort Star) = const $ VSort Box
    ty (VSort Box) = error "broken invariant"

sup_rule :: ElabCtx -> Clause -> Literal Value -> Clause -> Literal Value -> (Position, Value) -> Maybe Clause
sup_rule ctx (Cl d') (t :≈ t') (Cl c') ss' (upos, u)
  | applies =
      Just $ subst_clause sig $ Cl $ res : d' <> c'
  where
    c = Cl $ ss' : c'
    d = Cl $ (t :≈ t') : d'
    not_deep_occ_var (VFree m _) = not $ occurs_deeply ctx m c
    not_deep_occ_var _ = True
    sig = csu_select $ csu ctx $ Uc (t, u)
    ss'sig = apply_subst sig <$> ss'
    (tsig, t'sig) = (apply_subst sig t, apply_subst sig t')
    res = case ss' of
      s :≈ s' -> green_replace upos t' s :≈ s'
      s :≉ s' -> green_replace upos t' s :≉ s'
    applies =
      -- 1
      not (is_fluid_val u)
        -- 2
        && not_deep_occ_var u
        -- 3
        && varcond u tsig t'sig
        -- 5
        && ckbo tsig t'sig `notElem` ([Just LT, Just EQ] :: [PartialOrd])
        -- 6
        && ckbo (lfst ss'sig) (lsnd ss'sig) `notElem` ([Just LT, Just EQ] :: [PartialOrd])
        -- 8
        && eligible True (tsig :≈ t'sig) sig d
        -- 9
        && case ss' of
          Pos _ -> eligible True ss'sig sig c
          Neg _ -> eligible False ss'sig sig c
sup_rule _ _ _ _ _ _ = Nothing

-- TODO: it seems the rules apply the σ ∈ csu substitution greedily. so we don't really need
--   to return an ElabCtx, a fresh counter capability would suffice
fluidsup_rule ::
  ElabCtx
  -> Clause
  -> Literal Value
  -> Clause
  -> Literal Value
  -> (Position, Value)
  -> Maybe (Clause, ElabCtx)
fluidsup_rule ctx (Cl d') (t :≈ t') (Cl c') ss' (upos, u)
  | applies =
      Just (subst_clause sig $ Cl $ res : d' <> c', ctx')
  where
    c = Cl $ ss' : c'
    d = Cl $ (t :≈ t') : d'
    deep_occ_var (VFree m _) = occurs_deeply ctx m c
    deep_occ_var _ = False
    zm = fresh_meta ctx.metactx
    zty = fluid_head_ty u t'
    z = VFree zm zty
    ctx' = ctx{metactx = update_subst ctx.metactx zm (zty, Fresh Fluidsup)}
    -- TODO: where to force? also in 4. this is nonsense. we force with va, then force again (apply_subst)...
    va = value_app ctx'.metactx
    sig = csu_select $ csu ctx $ Uc (z `va` t, u)
    ss'sig = apply_subst sig <$> ss'
    (tsig, t'sig) = (apply_subst sig t, apply_subst sig t')
    res = case ss' of
      s :≈ s' -> green_replace upos (z `va` t') s :≈ s'
      s :≉ s' -> green_replace upos (z `va` t') s :≉ s'
    applies =
      -- 1
      (is_fluid_val u || deep_occ_var u)
        -- 4
        -- TODO: why syntactic equality? can we use αβη-conv?
        && not (abe_conv ctx'.metactx (apply_subst sig $ z `va` t') (apply_subst sig $ z `va` t))
        -- 5
        && ckbo tsig t'sig `notElem` ([Just LT, Just EQ] :: [PartialOrd])
        -- 6
        && ckbo (lfst ss'sig) (lsnd ss'sig) `notElem` ([Just LT, Just EQ] :: [PartialOrd])
        -- 8
        && eligible True (tsig :≈ t'sig) sig d
        -- 9
        && case ss' of
          Pos _ -> eligible True ss'sig sig c
          Neg _ -> eligible False ss'sig sig c
fluidsup_rule _ _ _ _ _ _ = Nothing

eres_rule :: ElabCtx -> Clause -> Literal Value -> Maybe Clause
eres_rule ctx (Cl c') (u :≉ u') | applies = Just $ subst_clause sig (Cl c')
  where
    c = Cl $ (u :≉ u') : c'
    sig = csu_select $ csu ctx $ Uc (u, u')
    applies = eligible False (apply_subst sig <$> (u :≉ u')) sig c
eres_rule _ _ _ = Nothing

efact_rule :: ElabCtx -> Clause -> Literal Value -> Literal Value -> Maybe Clause
efact_rule ctx (Cl c') (u' :≈ v') (u :≈ v)
  | applies =
      Just $ subst_clause sig $ Cl $ res <> c'
  where
    c = Cl $ (u' :≈ v') : (u :≈ v) : c'
    sig = csu_select $ csu ctx $ Uc (u, u')
    (usig, vsig) = (apply_subst sig u, apply_subst sig v)
    res = [v :≉ v', u :≈ v']
    applies =
      ckbo usig vsig `notElem` ([Just LT, Just EQ] :: [PartialOrd])
        && eligible False (usig :≈ vsig) sig c
efact_rule _ _ _ _ = Nothing
