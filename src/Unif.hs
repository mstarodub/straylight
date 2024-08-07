module Unif where

import Control.Exception (assert)
import Control.Monad
import Control.Monad.State
import Data.Bifunctor
import Data.Foldable
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import Data.Semigroup
import Debug.Trace
import qualified GHC.Exts (IsList, Item, fromList, toList)

import Elab
import Order ()

-- algorithm from "efficient full higher-order unification" by Bentkamp et al

-- debug_print
uf_trace :: ElabCtx -> [String] -> a -> a
uf_trace ctx ss x =
  if True then trace ("TRACE " <> show ctx.dbg_unif <> " " <> unwords ss) x else x

instance (Ord a) => GHC.Exts.IsList (MultiSet a) where
  type Item (MultiSet a) = a
  fromList = MultiSet.fromList
  toList = MultiSet.toList

newtype Stream a = Stream [a]
  deriving (GHC.Exts.IsList) via [a]
  deriving (Functor) via []
deriving via [a] instance Show a => Show (Stream a)

-- not lawful, doesn't matter
-- we need control over the monoid instance because we use foldMap
instance Semigroup (Stream a) where
  Stream as <> Stream bs = Stream (as `lazy_interleave` bs)
    where
      lazy_interleave :: [a] -> [a] -> [a]
      lazy_interleave [] ys = ys
      lazy_interleave (x : xs) ys = x : lazy_interleave ys xs
instance Monoid (Stream a) where
  mempty = []

-- setup:
-- s ?= t, both in hnf.
-- hnf: Lam x1 $ Lam x2 $ ... Lam xn $ a t1 t2 ... tp
-- (n ≥ 0, p ≥ 0)
-- where a is free var, bound var or constant
-- a flex iff a free variable, rigid otherwise (∈ Constants ∪ {x₁, ..., xₙ})
-- invariant: both sides have the same type

-- TODO: we use non-syntactic value equality/abe_conv in several places during unification:
--   1. in bind operations to check type equality (fine until we have dependent types...)?
--   2. for the delete transition. there, it seems fine to delete eagerly, since all that does is skip norm_a / decompose

-- reuse the value order for the unif constraints multiset.
-- hashing does not work since the hash function would be up to normalized terms,
-- as the only way to get Eq on values is to use abe_conv, but the unif constraints
-- would not necessarily be normalized.
-- the best data structure to represent sets would be a discrimination tree.
newtype UnifConstraint = Uc (Value, Value) deriving (Ord) via (Value, Value)

-- using abe_conv as the equality check poses no problems for the unification constraints:
-- syntactically equal values, which is what we actually want there:
--   have to normalize to the same thing
--   but syntactically nonequal values that are repeatedly reduced to hnf only normalize to the same thing
--   when a larger metacontext is used for conversion (which is never the case)
-- so it is indeed acceptable to use abe_conv.
-- TODO: switch to lists
-- TODO: re-check the constraints on each binding!
newtype UnifConstraints = Ucs (MultiSet UnifConstraint)

-- unoriented syntactic equality for constraints
instance Eq UnifConstraint where
  Uc (c1, c2) == Uc (d1, d2) =
    (c1 == d1 && c2 == d2)
      || (c1 == d2 && c2 == d1)

show_uc :: ElabCtx -> UnifConstraint -> String
show_uc ctx (Uc (v1, v2)) = show_val ctx v1 <> " ?= " <> show_val ctx v2

type UnifNode = Either LeafTy NodeState
data LeafTy = Unifier ElabCtx | Deadend
type NodeState = (UnifConstraints, ElabCtx)

get_n_unif :: Int -> ElabCtx -> UnifConstraint -> [Substitutions]
get_n_unif n ctx uc = let Stream ufs = csu ctx uc in take n ufs

-- CSU(t1, t2) === set of unifiers for t1, t2 U. ∀o unifier of t1, t2. ∃u∈U, substitution s. o ⊆ u
-- TODO: problem with this definition. why s needed here? can trivially pick s = o, then U = {id}
-- unifier: substitution s that makes terms t1, t2 abe-equiv: s t1 ↔(abe) s t2
-- MGU = one element CSU
csu :: ElabCtx -> UnifConstraint -> Stream Substitutions
csu ctx uc = extr_substs . unify $ [Right (Ucs [uc], ctx)]
  where
    extr_substs (Stream xs) = Stream [ct.metactx | Left (Unifier ct) <- xs]

unify :: Stream UnifNode -> Stream UnifNode
unify [] = []
unify (Stream (x : xs)) | Left (Unifier _) <- x = [x] <> (unify . unifstep $ Stream xs)
unify xs = unify $ unifstep xs

-- for all non-leaf nodes, all possible selected constraints, apply the rule that matches
unifstep :: Stream UnifNode -> Stream UnifNode
unifstep (Stream []) = []
-- succeed transition happens here
unifstep (Stream (Right (Ucs [], ctx) : tree)) = [Left $ Unifier ctx] <> unifstep (Stream tree)
-- branch out using our interleaving lazy concat monoid
unifstep (Stream (Right (Ucs ucs, ctx) : tree)) = foldMap f ucs <> unifstep (Stream tree)
  where
    f :: UnifConstraint -> Stream UnifNode
    f selected = transition (Ucs $ selected `MultiSet.delete` ucs, ctx) selected
-- prune failures
unifstep (Stream (Left Deadend : tree)) = unifstep $ Stream tree
-- preserve successes
unifstep (Stream (leafunif : tree)) = [leafunif] <> unifstep (Stream tree)

-- given (E, ctx containing the substitution) and a selected constraint, return all applicable transition results
transition :: NodeState -> UnifConstraint -> Stream UnifNode
-- normalize_b + dereference
transition (Ucs e, ctx) c =
  let Uc (sel1, sel2) = strip_abstr ctx.lvl c
  in go $ Uc (force ctx sel1, force ctx sel2)
  where
    go :: UnifConstraint -> Stream UnifNode
    -- fail
    go (Uc (VRigid a _, VRigid b _)) | a /= b = uf_trace ctx ["rule fail"] $ [Left Deadend]
    go (Uc (s, t))
      -- delete
      | s `abe_conv` t = uf_trace ctx ["rule delete", show_uc ctx $ Uc (s, t)] $ [Right (Ucs e, dbg_incdepth ctx)]
      -- decompose + bind
      | otherwise =
          uf_trace ctx ["rule decomp/bind", show_uc ctx $ Uc (s, t), show ctx] $
            let
              decomp = case decomp_possible s t of
                Just (sp1, sp2) ->
                  let new_decomposed = MultiSet.fromList . fmap Uc $ zip (toList sp1) (toList sp2)
                  in [ Right
                        ( Ucs $ e `MultiSet.union` new_decomposed
                        , ctx{dbg_unif = second (const "decomp") (dbg_incdepth ctx).dbg_unif}
                        )
                     ]
                Nothing -> []
              bind =
                fmap
                  (\ct -> Right (Ucs (Uc (s, t) `MultiSet.insert` e), ct))
                  (param (dbg_incdepth ctx) (Uc (s, t)))
            in
              let Stream decomp_bind = decomp <> bind
              in -- param can potentially return an empty list, like in λx.x ?= λx.F : (Bool → Nat) → (Bool → Nat)
                 -- this turns [] into a failure leaf
                 if null decomp_bind then [Left Deadend] else Stream decomp_bind
    -- TODO: also useful for restricting "fuel" (to be implemented)
    dbg_incdepth :: ElabCtx -> ElabCtx
    dbg_incdepth ct = ct{dbg_unif = first (+ 1) ct.dbg_unif}
    decomp_possible :: Value -> Value -> Maybe (Spine, Spine)
    decomp_possible (VRigid h1 s1) (VRigid h2 s2) =
      guard (h1 == h2 && length s1 == length s2) >> pure (s1, s2)
    decomp_possible (VFlex h1 s1) (VFlex h2 s2) =
      guard (h1 == h2 && length s1 == length s2) >> pure (s1, s2)
    decomp_possible _ _ = Nothing

param :: ElabCtx -> UnifConstraint -> Stream ElabCtx
param = param_complete

param_complete :: ElabCtx -> UnifConstraint -> Stream ElabCtx
param_complete ctx c = case c of
  Uc (VRigid _ _, VRigid _ _) -> []
  Uc (VFlex f _, VRigid a _) ->
    uf_trace ctx ["flex/rigid"] $
      let im = case a of
            Left _ -> []
            Right g -> [imit_bind ctx f g]
      in im <> (subst_unless ctx f Ident $ huet_bind ctx f)
  Uc (VRigid g sp1, VFlex f sp2) ->
    param_complete ctx (Uc (VFlex f sp2, VRigid g sp1))
  Uc (VFlex f1 _, VFlex f2 _)
    | f1 == f2 ->
        uf_trace ctx ["flex/flex, same head"] $
          subst_unless ctx f1 Elim $
            (iter_bind is_fun_ty ctx f1) <> (elim_bind ctx f1)
  Uc (VFlex f1 _, VFlex f2 _)
    | otherwise ->
        uf_trace ctx ["flex/flex, diff head"] $
          sconcat
            [ subst_unless ctx f1 Ident $ jp_bind ctx f1
            , subst_unless ctx f2 Ident $ jp_bind ctx f2
            , [ident_bind ctx f1 f2]
            , iter_bind (const True) ctx f1
            , iter_bind (const True) ctx f2
            ]
  Uc (_, _) -> []

param_pragmatic :: ElabCtx -> UnifConstraint -> Stream ElabCtx
param_pragmatic ctx c = case c of
  Uc (VRigid _ _, VRigid _ _) -> []
  Uc (VFlex f _, VRigid a _) ->
    let im = case a of
          Left _ -> []
          Right g -> [imit_bind ctx f g]
    in im <> (subst_unless ctx f Ident $ huet_bind ctx f)
  Uc (VRigid g sp1, VFlex f sp2) ->
    param_complete ctx (Uc (VFlex f sp2, VRigid g sp1))
  Uc (VFlex f1 _, VFlex f2 _)
    | f1 == f2 -> subst_unless ctx f1 Elim $ elim_bind ctx f1
    | otherwise -> [ident_bind ctx f1 f2] <> (subst_unless ctx f1 Ident $ huet_bind ctx f1)
  Uc (_, _) -> []

-- the abstractions have to be the same for all unification transitions
-- except for normalize_ae, which we get for free with values - so get rid of them
-- TODO: doesn't really need the level, can always start with 0
strip_abstr :: Lvl -> UnifConstraint -> UnifConstraint
strip_abstr l (Uc (VLam _ b1, VLam _ b2)) = strip_abstr (l + 1) $ Uc (b1 $ VBound l, b2 $ VBound l)
strip_abstr l (Uc ((VLam _ b), v)) = strip_abstr (l + 1) $ Uc (b $ VBound l, v `value_app` VBound l)
strip_abstr l (Uc (v, (VLam _ b))) = strip_abstr (l + 1) $ Uc (v `value_app` VBound l, b $ VBound l)
strip_abstr _ (Uc (v1, v2)) = Uc (v1, v2)

subst_unless :: ElabCtx -> Metavar -> EmergedFrom -> Stream ElabCtx -> Stream ElabCtx
subst_unless ctx m exclude res = case get_free_status_partial ctx m of
  Fresh x | x == exclude -> []
  Fresh _ -> res
  Substituted _ -> error "broken invariant: should not re-substitute"

-- uses nondeterminism / list monad. for each element in the list, there is one return
-- value where it appears (True), and one where it does not does not (False).
-- we do not want the original list, so we drop that
subseqs :: [a] -> [[a]]
subseqs = drop 1 . filterM (const [True, False])

-- TODO: all of these should be constructed as raw terms and made to terms by check, guarantees well-typedness

-- given a metavariable to substitute, its type, the term value it should be substituted by,
-- and the context it should be substituted in - return the new context containing the substitution
-- second to last arg is for debug printing
modif_metactx :: Metavar -> Value -> Term -> String -> ElabCtx -> ElabCtx
modif_metactx (Metavar m) mty replacee dbg_lastbind ctx =
  ctx
    { metactx = IntMap.insert m (mty, Substituted $ eval ctx replacee) ctx.metactx
    , dbg_unif = second (const dbg_lastbind) ctx.dbg_unif
    }

-- TODO: print xₙ to examine id fail
-- construct nabs lambda abstractions around a spine of applications body_1 ... body_n base
mk_lam :: Term -> [Term] -> Int -> Term
mk_lam base body nabs = iterate (Lam "x") (foldl (:@) base body) !! nabs

-- construct the type tys_1 -> ... -> tys_n -> base
mk_pi :: Value -> [Value] -> Value
mk_pi base tys = foldr construct_arr_val base tys

-- in most of the bind rules we want to generate a spine of the shape [(F₁ x₁ ... xₙ), ..., (Fₘ x₁ ... xₙ)],
-- where the Fᵢs are fresh metavariables. so, given an m, a way to get the type of Fᵢ given i, and n,
-- this helper returns a stateful computation that generates the spine given an initial context state,
-- with the state updated to a context in which all the fresh Fᵢs 'have been inserted
gen_apps :: Int -> (Int -> Value) -> Int -> State ElabCtx [Term]
gen_apps 0 _ _ = pure []
gen_apps m genty n = do
  ctx <- get
  let Metavar nm = fresh_meta ctx
  let mty = genty (m - 1)
  put $ ctx{metactx = IntMap.insert nm (mty, Fresh Other) ctx.metactx}
  rest <- gen_apps (m - 1) genty n
  let hd = Free (Metavar nm)
  let apps = foldl (:@) hd $ fmap (Bound . Idx) ([n - 1, n - 2 .. 0] :: [Int])
  pure (apps : rest)

ident_bind :: ElabCtx -> Metavar -> Metavar -> ElabCtx
ident_bind ctx f g =
  uf_trace ctx ["bind ident", "g_repby", show g, "|->", show g_replaceby, "f_repby", show f, "|->", show f_replaceby] $
    modif_metactx g g_ty g_replaceby "ident" $
      modif_metactx f f_ty f_replaceby "ident" newctx
  where
    f_replaceby = mk_lam h (xns <> fi_apps) n
    g_replaceby = mk_lam h (gi_apps <> yms) m
    ((fi_apps, gi_apps), newctx) = runState (liftM2 (,) gen_fi_apps gen_gj_apps) ctx'
    (h, ctx') =
      let
        Metavar mh = fresh_meta ctx
        hty = foldr construct_arr_val beta (f_alphas <> g_gammas)
      in
        (Free (Metavar mh), ctx{metactx = IntMap.insert mh (hty, Fresh Ident) ctx.metactx})
    (f_ty, g_ty) = (get_free_ty_partial ctx f, get_free_ty_partial ctx g)
    f_tys = destruct_arr_val ctx f_ty
    g_tys = destruct_arr_val ctx g_ty
    (f_alphas, g_gammas) = assert (last f_tys `abe_conv` last g_tys) $ (init f_tys, init g_tys)
    beta = last f_tys
    n = length f_alphas
    m = length g_gammas
    xns = fmap (Bound . Idx) ([n - 1, n - 2 .. 0] :: [Int])
    yms = fmap (Bound . Idx) ([m - 1, m - 2 .. 0] :: [Int])
    gen_fi_apps = gen_apps m (\i -> mk_pi (g_gammas !! i) f_alphas) n
    gen_gj_apps = gen_apps n (\j -> mk_pi (f_alphas !! j) g_gammas) m

-- modify f (free) to Substituted v, where v is the constructed lambda
-- return the new context in which f has been substituted
imit_bind :: ElabCtx -> Metavar -> Name -> ElabCtx
imit_bind ctx f g =
  uf_trace ctx ["bind imit"] $
    modif_metactx f f_ty f_replaceby "imit" newctx
  where
    f_replaceby = mk_lam (Const g) fi_apps n
    (fi_apps, newctx) = runState gen_fi_apps ctx
    (f_ty, g_ty) = (get_free_ty_partial ctx f, get_const_ty_partial ctx g)
    f_tys = destruct_arr_val ctx f_ty
    g_tys = destruct_arr_val ctx g_ty
    (f_alphas, g_gammas) = assert (last f_tys `abe_conv` last g_tys) (init f_tys, init g_tys)
    n = length f_alphas
    m = length g_gammas
    gen_fi_apps = gen_apps m (\i -> mk_pi (g_gammas !! i) f_alphas) n

elim_bind :: ElabCtx -> Metavar -> Stream ElabCtx
elim_bind ctx f =
  uf_trace ctx ["bind elim"] $
    Stream (fmap modif_for_subseq (subseqs [0 .. n - 1]))
  where
    f_ty = get_free_ty_partial ctx f
    f_tys = destruct_arr_val ctx f_ty
    f_alphas = assert (not . null . init $ f_tys) $ init f_tys
    beta = last f_tys
    n = length f_alphas
    modif_for_subseq :: [Int] -> ElabCtx
    modif_for_subseq subs = modif_metactx f f_ty f_replaceby "elim" newctx
      where
        f_replaceby = mk_lam g xjs n
        xjs = fmap (Bound . Idx) subs
        (g, newctx) =
          let
            Metavar mg = fresh_meta ctx
            gty = foldr construct_arr_val beta (fmap (f_alphas !!) subs)
          in
            (Free (Metavar mg), ctx{metactx = IntMap.insert mg (gty, Fresh Elim) ctx.metactx})

huet_jp_bind :: (Value -> Bool) -> ElabCtx -> Metavar -> Stream ElabCtx
huet_jp_bind prop ctx f = Stream . catMaybes $ fmap modif_for_selected (zip [0 ..] (filter prop f_alphas))
  where
    f_ty = get_free_ty_partial ctx f
    f_tys = destruct_arr_val ctx f_ty
    f_alphas = assert (not . null . init $ f_tys) $ init f_tys
    beta = last f_tys
    n = length f_alphas
    modif_for_selected :: (Int, Value) -> Maybe ElabCtx
    modif_for_selected (ai_idx, ai) =
      if beta `abe_conv` last a_tys
        then Just (modif_metactx f f_ty f_replaceby "huet/jp" newctx)
        else Nothing
      where
        f_replaceby = mk_lam xi fi_apps n
        xi = Bound . Idx $ n - 1 - ai_idx
        (fi_apps, newctx) = runState gen_fi_apps ctx
        a_tys = destruct_arr_val ctx ai
        a_gammas = init a_tys
        m = length a_gammas
        gen_fi_apps = gen_apps m (\i -> mk_pi (a_gammas !! i) f_alphas) n

huet_bind :: ElabCtx -> Metavar -> Stream ElabCtx
huet_bind ctx f =
  uf_trace ctx ["bind huet"] $
    huet_jp_bind (const True) ctx f

jp_bind :: ElabCtx -> Metavar -> Stream ElabCtx
jp_bind ctx f =
  uf_trace ctx ["bind jp"] $
    huet_jp_bind (not . is_fun_ty) ctx f

is_fun_ty :: Value -> Bool
is_fun_ty (VPi _ _ _) = True
is_fun_ty _ = False

-- TODO: is broken
-- TODO: JP, page 14: regard types deltas as variables themselves, as they behave like "dummies". is this really ok?
iter_bind :: (Value -> Bool) -> ElabCtx -> Metavar -> Stream ElabCtx
iter_bind prop ctx f =
  uf_trace ctx ["bind iter"] $
    sconcat (fmap modif_for_d_abstractions [0 ..])
  where
    modif_for_d_abstractions :: Int -> Stream ElabCtx
    modif_for_d_abstractions d = Stream $ fmap modif_for_selected (zip [0 ..] (filter prop f_alphas))
      where
        f_ty = get_free_ty_partial ctx f
        f_tys = destruct_arr_val ctx f_ty
        f_alphas = assert (not . null . init $ f_tys) $ init f_tys
        beta1 = last f_tys
        n = length f_alphas
        xns = fmap (Bound . Idx) ([n - 1, n - 2 .. 0] :: [Int])
        (deltas, ctx') = runState (gen_deltas d) ctx
        gen_deltas :: Int -> State ElabCtx [Value]
        gen_deltas j = replicateM j $ do
          ct <- get
          let Metavar nm = fresh_meta ct
          let mty = VSort Star
          put $ ctx{metactx = IntMap.insert nm (mty, Fresh Dummy) ctx.metactx}
          pure $ VFree (Metavar nm)
        modif_for_selected :: (Int, Value) -> ElabCtx
        modif_for_selected (ai_idx, ai) = modif_metactx f f_ty f_replaceby "iter" newctx
          where
            f_replaceby = mk_lam h (xns <> [iter_lam_gis]) n
            (gi_apps, newctx) = runState gen_gj_apps ctx''
            iter_lam_gis = mk_lam xi gi_apps d
            xi = Bound . Idx $ n - 1 - ai_idx
            a_tys = destruct_arr_val ctx ai
            a_gammas = init a_tys
            beta2 = last a_tys
            m = length a_gammas
            (h, ctx'') =
              let
                Metavar mh = fresh_meta ctx'
                deltas_to_b2 = foldr construct_arr_val beta2 deltas
                hty = foldr construct_arr_val beta1 (f_alphas <> [deltas_to_b2])
              in
                (Free (Metavar mh), ctx{metactx = IntMap.insert mh (hty, Fresh Other) ctx.metactx})
            gen_gj_apps = gen_apps m (\j -> mk_pi (a_gammas !! j) (f_alphas <> deltas)) (n + d)

construct_arr_val :: Value -> Value -> Value
construct_arr_val l r = VPi "" l (const r)

-- we assume nondependent function types only here. this function will wreak havoc otherwise
-- ghci> destruct_arr_val ctx $ get_const_ty_partial ctx "add'"
-- [VFlex 1 (fromList []),VFlex 1 (fromList []),VPi "" (VFlex 1 (fromList [])) <function>,VSort □,VPi "N" (VSort □) <function>,VPi "N" (VSort □) <function>]
-- ghci> get_const_ty_partial ctx "add'"
-- VPi "" (VPi "N" (VSort □) <function>) <function>
-- TODO: what about parametric polymorphism, does the fact that "everything is fully applied" gurantee this is ok?
destruct_arr_val :: ElabCtx -> Value -> [Value]
destruct_arr_val ctx (VPi _ l r) = l : destruct_arr_val ctx (r $ dummy_val)
  where
    dummy_val = VFree $ fresh_meta ctx
destruct_arr_val _ v = [v]
