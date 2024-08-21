module Elab where

import Control.Monad
import Control.Monad.Except
import Data.Bifunctor
import Data.Either
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.Sequence (Seq (..))
import Debug.Trace
import GHC.Exts (toList)
import Numeric.Natural
import Text.Megaparsec (SourcePos, errorBundlePretty, initialPos, sourcePosPretty)

import Core
import Parse
import Pretty

-- alpha convertibility.
-- almost syntactic equality (but we are ignoring the binder names)
instance Eq Term where
  -- invariant: no two consts with the same name
  Const c1 == Const c2 = c1 == c2
  Free v1 == Free v2 = v1 == v2
  Bound i1 == Bound i2 = i1 == i2
  ALam _ t1 b1 == ALam _ t2 b2 = t1 == t2 && b1 == b2
  Pi _ t1 t1' == Pi _ t2 t2' = t1 == t2 && t1' == t2'
  e1 :@ e1' == e2 :@ e2' = e1 == e2 && e1' == e2'
  Sort s1 == Sort s2 = s1 == s2
  _ == _ = False

-- add a bound variable
bind_var :: ElabCtx -> (Name, Value) -> ElabCtx
bind_var ctx (s, ty) =
  ctx
    { tenv = extend_ctx (s, ty) ctx.tenv
    , lenv = VBound ctx.lvl ty : ctx.lenv
    , lvl = ctx.lvl + 1
    }

-- extend toplevel with a proxy constant
define_const :: ElabCtx -> (Name, Value) -> ElabCtx
define_const ctx (s, ty) =
  ctx
    { toplvl = extend_ctx (s, (VConst s ty, ty)) ctx.toplvl
    }

-- extend toplevel with a constant
define_val :: ElabCtx -> (Name, Value, Value) -> ElabCtx
define_val ctx (s, v, ty) =
  ctx
    { toplvl = extend_ctx (s, (v, ty)) ctx.toplvl
    }

-- no checking for metas that are already present. will overwrite
define_free :: ElabCtx -> (Metavar, Value) -> ElabCtx
define_free ctx (Metavar m, ty) =
  ctx
    { metactx = IntMap.insert m (ty, Fresh User) ctx.metactx
    }

extend_lenv :: ElabCtx -> Value -> ElabCtx
extend_lenv ctx x = ctx{lenv = x : ctx.lenv}

get_const_def_partial :: ElabCtx -> Name -> Value
get_const_def_partial ctx n = fst $ lookup_ctx_partial ctx.toplvl n

get_const_ty_partial :: ElabCtx -> Name -> Value
get_const_ty_partial ctx n = snd $ lookup_ctx_partial ctx.toplvl n

get_free_def_partial :: ElabCtx -> Metavar -> Value
get_free_def_partial ctx m = VFree m $ get_free_ty_partial ctx m

already_defined :: ElabCtx -> Either Metavar Name -> Bool
already_defined ctx (Left (Metavar m)) = m `IntMap.member` ctx.metactx
already_defined ctx (Right s) = isRight $ lookup_ctx ctx.toplvl s

get_free_ty :: ElabCtx -> Metavar -> Either String Value
get_free_ty ctx (Metavar m) = case fst <$> ctx.metactx IntMap.!? m of
  Just v -> pure v
  Nothing -> throwError $ "cannot find type for free variable  ?" <> show m

get_free_ty_partial :: ElabCtx -> Metavar -> Value
get_free_ty_partial ctx (Metavar m) = fst $ ctx.metactx IntMap.! m

get_free_status_partial :: ElabCtx -> Metavar -> MetaStatus
get_free_status_partial ctx (Metavar m) = snd $ ctx.metactx IntMap.! m

update_subst :: Substitution -> Metavar -> (Value, MetaStatus) -> Substitution
update_subst sig (Metavar m) (mty, replacee) = IntMap.insert m (mty, replacee) sig

get_subst :: Substitution -> Metavar -> MetaStatus
get_subst sig (Metavar m) = snd $ sig IntMap.! m

id_subst :: Substitution
id_subst = IntMap.empty

-- next available metavar counter
-- caller is responsible for adding the entry!
fresh_meta :: Substitution -> Metavar
fresh_meta sig = Metavar $ maybe 0 ((+ 1) . fst) (IntMap.lookupMax sig)

get_arity :: Value -> Natural
get_arity (VPi _ _ b) = 1 + get_arity (b dummy_conv_val_unsafe)
get_arity _ = 0

dummy_conv_val_unsafe :: Value
dummy_conv_val_unsafe = VBound (-1) (VSort Box)

-- lvl_max = idx + lvl + 1 ⟺ idx = lvl_max - lvl - 1
lvl2idx :: Lvl -> Lvl -> Idx
lvl2idx (Lvl l) (Lvl x) = Idx $ l - x - 1

-- force a thunk after a substitution up to hnf. cannot pattern match on values otherwise
-- TODO: during forcing and in eval - do we delete the substituted meta from the ctx and return a new one?
force :: Substitution -> Value -> Value
force sig (VFlex m sp _)
  | Substituted v <- get_subst sig m =
      force sig (value_app_spine sig v sp)
force _ v = v

-- expensive
apply_subst :: Substitution -> Value -> Value
apply_subst sig (VFlex m sp _)
  | Substituted v <- get_subst sig m = apply_subst sig (value_app_spine sig v sp)
apply_subst sig (VRigid r sp a) = VRigid r (fmap (apply_subst sig) sp) a
apply_subst sig (VLam s va vb) = VLam s (apply_subst sig va) $ apply_subst sig . vb
apply_subst sig (VPi s v vb) = VPi s (apply_subst sig v) $ apply_subst sig . vb
apply_subst _ v = v

-- where the computation happens
value_app :: Substitution -> Value -> Value -> Value
value_app _ (VLam _ _ body) v = body v
value_app sig (VFlex s spine a) v = VFlex s (spine :|> v) (ty_app sig a v)
value_app sig (VRigid x spine a) v = VRigid x (spine :|> v) (ty_app sig a v)
value_app _ _ _ = error "impossible"

ty_app :: Substitution -> Value -> Value -> Value
ty_app sig a t = case force sig a of
  VPi _ _ b -> b t
  _ -> error "impossible"

-- apply single value to a spine
value_app_spine :: Substitution -> Value -> Spine -> Value
value_app_spine _ v Empty = v
value_app_spine sig v (spine :|> s) = value_app sig (value_app_spine sig v spine) s

-- normal form evaluation
eval :: ElabCtx -> Term -> Value
eval ctx (Const v) = get_const_def_partial ctx v
eval ctx (Free m) = case get_subst ctx.metactx m of
  Substituted v -> v
  Fresh _ -> VFree m (get_free_ty_partial ctx m)
eval ctx (Bound (Idx i)) = ctx.lenv `List.genericIndex` i
eval ctx (ALam s a body) = VLam s (eval ctx a) (\x -> eval (extend_lenv ctx x) body)
eval ctx (Pi ms t1 t2) = VPi ms (eval ctx t1) (\x -> eval (extend_lenv ctx x) t2)
eval ctx (e1 :@ e2) = value_app ctx.metactx (eval ctx e1) (eval ctx e2)
eval _ (Sort s) = VSort s

quote :: ElabCtx -> Value -> Term
quote ctx v = case force ctx.metactx v of
  VFlex s spine _ -> quote_spine (Free s) spine
  VRigid (Left x) spine _ -> quote_spine (Bound $ lvl2idx ctx.lvl x) spine
  VRigid (Right s) spine _ -> quote_spine (Const s) spine
  VLam s a body -> ALam s (quote ctx a) $ quote ctx' (body $ VBound ctx.lvl a)
  VPi s a body -> Pi s (quote ctx a) $ quote ctx' (body $ VBound ctx.lvl a)
  VSort s -> Sort s
  where
    ctx' = ctx{lvl = ctx.lvl + 1}
    quote_spine :: Term -> Spine -> Term
    quote_spine t Empty = t
    quote_spine t (spine :|> sp) = quote_spine t spine :@ quote ctx sp

quote_0_nonforcing :: Value -> Term
quote_0_nonforcing = go 0
  where
    go :: Lvl -> Value -> Term
    go l (VFlex s spine _) = go_spine l (Free s) spine
    go l (VRigid (Left x) spine _) = go_spine l (Bound $ lvl2idx l x) spine
    go l (VRigid (Right s) spine _) = go_spine l (Const s) spine
    go l (VLam s a body) = ALam s (go l a) $ go (l + 1) (body $ VBound l a)
    go l (VPi s a body) = Pi s (go l a) $ go (l + 1) (body $ VBound l a)
    go _ (VSort s) = Sort s
    go_spine :: Lvl -> Term -> Spine -> Term
    go_spine _ t Empty = t
    go_spine l t (spine :|> sp) = go_spine l t spine :@ go l sp

nf :: ElabCtx -> Term -> Term
nf ctx = quote ctx . eval ctx

eta_reduce :: Term -> Term
eta_reduce (ALam _ _ (t :@ Bound 0)) | not (0 `free_in` t) = shift_down t
  where
    -- only bound vars "outside" / free vars
    shift_down :: Term -> Term
    shift_down = go 0
      where
        -- c counts the number of binders we crossed
        go c (ALam s a b) = ALam s (go c a) (go (c + 1) b)
        go c (Pi s t1 t2) = Pi s (go c t1) (go (c + 1) t2)
        go c (t1 :@ t2) = go c t1 :@ go c t2
        go c (Bound i) | i == c = error "eta_reduce: broken invariant"
        go c (Bound i) | i > c = Bound $ i - 1
        go _ t1 = t1
eta_reduce (ALam s a t) = ALam s (eta_reduce a) (eta_reduce t)
eta_reduce (Pi s t1 t2) = Pi s (eta_reduce t1) (eta_reduce t2)
eta_reduce (t1 :@ t2) = eta_reduce t1 :@ eta_reduce t2
eta_reduce t = t

-- typechecking monad
type Tc = Except String
runTC = runExcept
runTC_partial = either error id . runTC

report :: ElabCtx -> String -> Tc a
report ctx msg = throwError $ sourcePosPretty ctx.srcpos <> ":\n" <> msg

-- debug printing
debug_tc = False
tc_trace :: [String] -> Tc ()
tc_trace ss =
  when debug_tc $ trace ("TRACE " <> unwords ss) $ () `seq` pure ()
tc_trace2 :: [String] -> Tc ()
tc_trace2 ss =
  trace ("TRACE2 " <> unwords ss) $ () `seq` pure ()

mk_ctx :: SourcePos -> [Raw] -> Tc ElabCtx
mk_ctx pos = build_ctx (ElabCtx [] [] 0 [] id_subst (0, "") pos Nothing)

grow_ctx :: SourcePos -> ElabCtx -> [Raw] -> Tc ElabCtx
grow_ctx pos ctx = build_ctx ctx{srcpos = pos}

-- invariant: we never infer or check RLet and RCLet. get rid of them by
-- folding over special toplevel dfns (lets and constants) with infer to typecheck and eval to create a value toplevel
-- we require all constants in the toplevel to be in topologically sorted order, so this is okay
build_ctx :: ElabCtx -> [Raw] -> Tc ElabCtx
build_ctx ct [] = pure ct
build_ctx ct (RSrcPos p rt : rw) = build_ctx ct{srcpos = p} (rt : rw)
build_ctx ct (RLet s rty rdef : rw) = do
  tc_trace ["mk_ctx / rlet", show s]
  when (already_defined ct (Right s)) $ report ct $ show s <> " is already defined"
  tmty <- infer ct rty
  let vty = eval ct . fst $ tmty
  tmv <- check ct rdef vty
  let vv = eval ct tmv
  let ct' = define_val ct (s, vv, vty)
  build_ctx ct' rw
build_ctx ct (RCLet s rty : rw) = do
  tc_trace ["mk_ctx / const", show s]
  when (already_defined ct (Right s)) $ report ct $ show s <> " is already defined"
  tmty <- infer ct rty
  let vty = eval ct . fst $ tmty
  let ct' = define_const ct (s, vty)
  build_ctx ct' rw
build_ctx ct (RFLet m rty : rw) = do
  tc_trace ["mk_ctx / free", show m]
  when (already_defined ct (Left m)) $ report ct $ show_term ct (Free m) <> " is already defined"
  tmty <- infer ct rty
  let vty = eval ct . fst $ tmty
  let ct' = define_free ct (m, vty)
  build_ctx ct' rw
build_ctx ct (RForm f : []) = do
  tfd <- traverse (traverse (traverse tf)) f
  pure ct{problem = Just $ fmap Cl tfd}
  where
    tf :: Raw -> Tc Value
    tf x = do
      (tm, _) <- infer ct x
      pure $ eval ct tm
build_ctx ct (_ : _) = report ct "invalid toplevel"

empty_ctx :: ElabCtx
empty_ctx = ctx_fromraw []

ctx_fromraw :: [Raw] -> ElabCtx
ctx_fromraw = runTC_partial . mk_ctx (initialPos "input")

infer :: ElabCtx -> Raw -> Tc (Term, Value)
infer ctx (RSrcPos pos r) = infer ctx{srcpos = pos} r
-- try toplvl and tenv, since the var could be bound or a const
infer ctx (RVar s) =
  (first Bound <$> liftEither (lookup_ctx_idx ctx.tenv s))
    `catchError` const ((Const s,) . snd <$> liftEither (lookup_ctx ctx.toplvl s))
    `catchError` report ctx
infer ctx (RFree m) = do
  vty <- liftEither (get_free_ty ctx m) `catchError` report ctx
  pure (Free m, vty)
infer ctx (RApp r1 r2) = do
  tc_trace ["infer: rapp", show (RApp r1 r2)]
  (tm1, ty1) <- infer ctx r1
  case ty1 of
    VPi _ a b -> do
      tm2 <- check ctx r2 a
      pure (tm1 :@ tm2, b (eval ctx tm2))
    _ -> report ctx $ "non-function in head of application - " <> show_term ctx tm1 <> " : " <> show_val ctx ty1
infer ctx (RPi s t1 t2) = do
  tc_trace ["infer: rpi", show (RPi s t1 t2)]
  (tm1, s1) <- infer ctx t1
  let ctx' = bind_var ctx (s, eval ctx tm1)
  (tm2, s2) <- infer ctx' t2
  check_rule ctx (s1, s2)
  pure (Pi s tm1 tm2, s2)
infer _ RStar = pure (Sort Star, VSort Box)
infer ctx (RALam s ty body) = do
  tc_trace ["infer: ralam", show (RALam s ty body)]
  (tmty, _) <- infer ctx ty
  let tmv = eval ctx tmty
  let ctx' = bind_var ctx (s, tmv)
  (tmb, tyb) <- infer ctx' body
  -- this part is a bit tricky, but similar to how we eval lams and pis
  let rettyc = quote ctx{lvl = ctx.lvl + 1} tyb
  let retty = \v -> eval (extend_lenv ctx v) rettyc
  pure (ALam s tmty tmb, VPi s tmv retty)
infer ctx e = report ctx $ "unable to infer type for " <> show e

check :: ElabCtx -> Raw -> Value -> Tc Term
check ctx (RSrcPos pos r) v = check ctx{srcpos = pos} r v
check ctx (RLam s body) (VPi _ vt vf) = do
  tc_trace ["check: rlam/vpi", show (RLam s body), show_val ctx (VPi "" vt vf)]
  let ctx' = bind_var ctx (s, vt)
  tm <- check ctx' body (vf (VBound ctx.lvl vt))
  pure $ ALam s (quote ctx vt) tm
check ctx r vty_want = do
  tc_trace ["check: other", show r, show_val ctx vty_want]
  (tm, vty_have) <- infer ctx r
  unless (abe_conv ctx.metactx vty_want vty_have) $
    report ctx $
      "expected " <> show_val ctx vty_want <> "\ngot type " <> show_val ctx vty_have
  pure tm

check_rule :: ElabCtx -> (Value, Value) -> Tc ()
check_rule ctx (VSort s1, VSort s2) = when ((s1, s2) `notElem` allowed_rules) $ report ctx $ "bad dependency " <> show (s1, s2)
  where
    allowed_rules :: [(Sorts, Sorts)]
    allowed_rules = [(Star, Star), (Box, Box), (Box, Star)]
check_rule ctx (x1, x2) = report ctx $ "not a sort: " <> show (show_val ctx x1, show_val ctx x2)

-- precondition: both values have the same type
-- this does not perform unification
-- instead of comparing terms after quoting,
-- we can do fast conversion checking on values directly
-- use special conversion variables with fresh names by abusing the VBound constructor together with negative levels
-- these conversion variables are invalid outside of and only used for conversion checking
abe_conv :: Substitution -> Value -> Value -> Bool
abe_conv sig = go (-1)
  where
    go :: Lvl -> Value -> Value -> Bool
    go _ (VSort s1) (VSort s2) = s1 == s2
    go l (VLam _ a b1) (VLam _ _ b2) = go (l - 1) (b1 $ VBound l a) (b2 $ VBound l a)
    go l (VFlex s1 sp1 _) (VFlex s2 sp2 _) = s1 == s2 && go_spine l sp1 sp2
    go l (VRigid x1 sp1 _) (VRigid x2 sp2 _) = x1 == x2 && go_spine l sp1 sp2
    go l (VPi _ a1 b1) (VPi _ a2 b2) = go l a1 a2 && go (l - 1) (b1 $ VBound l a1) (b2 $ VBound l a1)
    -- syntax-directed eta equality cases
    go l v (VLam _ a b) = go (l - 1) (value_app sig v $ VBound l a) (b $ VBound l a)
    go l (VLam _ a b) v = go (l - 1) (b $ VBound l a) (value_app sig v $ VBound l a)
    go _ _ _ = False
    go_spine :: Lvl -> Spine -> Spine -> Bool
    go_spine _ Empty Empty = True
    go_spine l (spine1 :|> sp1) (spine2 :|> sp2) =
      go l sp1 sp2 && go_spine l spine1 spine2
    go_spine _ _ _ = False

show_val :: ElabCtx -> Value -> String
show_val ctx = show_term ctx . quote ctx

-- for debugging
instance Show ElabCtx where
  show ctx =
    "env = [\n"
      <> pp_zipped_ctx (zipWith (\a (b, c) -> (b, (a, c))) ctx.lenv $ toList ctx.tenv)
      <> "\n] metactx = [\n"
      <> pp_substitutions ctx ctx.metactx
      <> "] toplvl = [\n"
      <> pp_zipped_ctx tlvl
      <> "\n]"
    where
      Ctx tlvl = ctx.toplvl
      pp_zipped_ctx :: [(Name, (Value, Value))] -> String
      pp_zipped_ctx xs = List.intercalate "\n" $ fmap go xs
        where
          go (Name s, (val, vty)) =
            "\t"
              <> s
              <> " : "
              <> show_val ctx vty
              <> " = "
              <> show_val ctx val
      pp_substitutions :: ElabCtx -> Substitution -> String
      pp_substitutions ct =
        IntMap.foldMapWithKey
          \key (val, status) ->
            "\t?"
              <> show key
              <> " : "
              <> show_val ct val
              <> " -- "
              <> pp_metastatus ct status
              <> "\n"
      pp_metastatus :: ElabCtx -> MetaStatus -> String
      pp_metastatus _ (Fresh from) = show from
      pp_metastatus ct (Substituted v) = "Substituted " <> show_val ct v

append_parse_tc_toplvl :: String -> ElabCtx -> String -> ElabCtx
append_parse_tc_toplvl filename ctx contents =
  case parse_raw filename contents of
    Left e -> do
      error $ errorBundlePretty e
    Right rs -> do
      let ctx' = grow_ctx (initialPos filename) ctx rs
      case runTC ctx' of
        Left e -> error $ display_err contents e
        Right r -> r

parse_tc_toplvl :: String -> String -> ElabCtx
parse_tc_toplvl filename = append_parse_tc_toplvl filename empty_ctx

append_input_str :: ElabCtx -> [String] -> ElabCtx
append_input_str ctx = append_parse_tc_toplvl "input" ctx . unlines

input_str :: [String] -> ElabCtx
input_str = parse_tc_toplvl "input" . unlines

append_input_file :: ElabCtx -> String -> IO ElabCtx
append_input_file ctx filename = do
  contents <- readFile filename
  pure $ append_parse_tc_toplvl filename ctx contents

input_file :: String -> IO ElabCtx
input_file filename = do
  contents <- readFile filename
  pure $ parse_tc_toplvl filename contents
