module Elab where

import Control.Monad
import Control.Monad.Except
import Data.Bifunctor
import Data.Char
import Data.Either
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.Sequence (Seq (..))
import Data.String (IsString)
import Data.Void
import Debug.Trace
import GHC.Exts (IsList, toList)
import Numeric.Natural
import qualified System.Console.ANSI as Console
import Text.Megaparsec hiding (Stream)
import qualified Text.Megaparsec.Char as C (space1)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Printf
import Text.Show.Functions ()

-- setting:
-- type of all free variables is known
-- all polymorphic symbols have explicit type arguments

-- need:
--   type constructors (like maybe, list, bool)
--   term constants (of fixed type)
--   type/term variables (known type) "free"
--   example type constructor: const ttt = forall a:*. a -> bool

-- user-supplied presyntax. named representation
data Raw
  = -- used for everything except free variables. those are not present in user input, but we
    -- provide a constructor (RFLet) and a way of referring to them (RFree) for testing
    RVar Name
  | RApp Raw Raw
  | RLam Name Raw
  | RPi Name Raw Raw
  | RStar
  | RLet Name Raw Raw -- RLet x:a = t
  | RCLet Name Raw -- RCLet x:a
  | RFLet Metavar Raw -- RFLet x:a
  | RFree Metavar -- ?f
  | RSrcPos SourcePos Raw -- for error reporting
  deriving (Show)

newtype Name = Name String deriving (Semigroup, Show, Monoid, Ord, Eq, IsString) via String
newtype Metavar = Metavar Int deriving (Ord, Eq, Show, Num, Enum) via Int
newtype Idx = Idx Int deriving (Eq, Ord, Show, Num) via Int
newtype Lvl = Lvl Int deriving (Eq, Ord, Show, Num) via Int

-- ⋆ or □. ⋆ can be read as "type", and e.g. we have bool : ⋆.
-- additionally, ⋆:□, but boxes (□) are just for internal use by the typechecker and never present in input
data Sorts = Star | Box
  deriving (Eq, Ord)

-- we could drop the name from Lam and Pi, but we keep it around for pretty printing.
-- crucially, we do not keep it in the bound variable constructor - that one uses debruijn indices.
-- (knowing the name of the binder is enough to know the name of everything that refers to it)
-- name manipulation only happens in printing - freshness, shadowing etc is not a concern
-- for constants and free variables: their types (and values) are in the context, and they always have an associated type
-- names for those may not clash!
data Term
  = Const Name -- type constructors + term constants
  | Free Metavar -- free variables (type known)
  | Bound Idx -- debrujin index
  | Pi Name Term Term
  | Term :@ Term -- application
  | Sort Sorts
  | ALam Name Term Term

pattern (:->) :: Term -> Term -> Term
pattern a :-> b = Pi "" a b
infixr 1 :->

type Spine = Seq Value

data Value
  = VFlex Metavar Spine Value
  | VRigid (Either Lvl Name) Spine Value
  | VLam Name Value (Value -> Value)
  | VPi Name Value (Value -> Value)
  | VSort Sorts
  deriving (Show)

pattern VBound :: Lvl -> Value -> Value
pattern VBound x a = VRigid (Left x) [] a

-- proxy value (for a constant)
pattern VConst :: Name -> Value -> Value
pattern VConst x a = VRigid (Right x) [] a
pattern VFree :: Metavar -> Value -> Value
pattern VFree m a = VFlex m [] a

newtype Ctx a = Ctx [(Name, a)]
  deriving (IsList, Semigroup, Monoid, Show) via [(Name, a)]
  deriving (Functor)

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

lookup_ctx :: Ctx a -> Name -> Either String a
lookup_ctx (Ctx r) s = case lookup s r of
  Just t -> pure t
  Nothing -> throwError $ "cannot find variable " <> show s

lookup_ctx_partial :: Ctx a -> Name -> a
lookup_ctx_partial c = either error id . lookup_ctx c

extend_ctx :: (Name, a) -> Ctx a -> Ctx a
extend_ctx (s, t) (Ctx e) = Ctx $ (s, t) : e

lookup_ctx_idx :: Ctx a -> Name -> Either String (Idx, a)
lookup_ctx_idx (Ctx r) key = go 0 r
  where
    go _ [] = throwError $ "cannot find variable " <> show key
    go i ((s, x) : sxs)
      | key == s = pure $ (i, x)
      | otherwise = go (i + 1) sxs

lvl2idx :: Lvl -> Lvl -> Idx
lvl2idx (Lvl l) (Lvl x) = Idx $ l - x - 1

(!!!) :: [a] -> Idx -> a
xs !!! (Idx i) = xs `List.genericIndex` i

data EmergedFrom = Elim | Ident | Dummy | Skolem | User | Other
  deriving (Show, Eq)
data MetaStatus = Substituted Value | Fresh EmergedFrom
  deriving (Show)

type Substitutions = IntMap (Value, MetaStatus)

-- tenv is the typing context for bound variables, name-keyed (names come from raw terms)
-- lenv contains values (for eval)
-- toplvl stores (values,types) for let definitions
-- invariant: length (= lvl). "unzipped"
-- metactx stores types of free vars and their substitution state
-- unification debug info is (tree depth, "last bind op")
data ElabCtx = ElabCtx
  { tenv :: Ctx Value
  , lenv :: [Value]
  , lvl :: Lvl
  , toplvl :: Ctx (Value, Value)
  , metactx :: Substitutions
  , dbg_unif :: (Integer, String)
  , srcpos :: SourcePos
  }

already_defined :: ElabCtx -> Either Metavar Name -> Bool
already_defined ctx (Left (Metavar m)) = m `IntMap.member` ctx.metactx
already_defined ctx (Right s) = isRight $ lookup_ctx ctx.toplvl s

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

-- TODO: not needed? actually maybe it is during eval
get_free_ty :: ElabCtx -> Metavar -> Either String Value
get_free_ty ctx (Metavar m) = case fst <$> ctx.metactx IntMap.!? m of
  Just v -> pure v
  Nothing -> throwError $ "cannot find type for free variable  ?" <> show m
get_free_ty_partial :: ElabCtx -> Metavar -> Value
get_free_ty_partial ctx (Metavar m) = fst $ ctx.metactx IntMap.! m

get_free_status_partial :: ElabCtx -> Metavar -> MetaStatus
get_free_status_partial ctx (Metavar m) = snd $ ctx.metactx IntMap.! m

get_free_def_partial :: ElabCtx -> Metavar -> Value
get_free_def_partial ctx m = VFree m $ get_free_ty_partial ctx m

-- next available metavar counter
-- caller is responsible for adding the entry!
fresh_meta :: ElabCtx -> Metavar
fresh_meta ctx = Metavar $ maybe 0 ((+ 1) . fst) (IntMap.lookupMax ctx.metactx)

get_arity :: Value -> Natural
get_arity (VPi _ _ b) = 1 + get_arity (b dummy_conv_val_unsafe)
get_arity _ = 0

dummy_conv_val_unsafe :: Value
dummy_conv_val_unsafe = VBound (-1) (VSort Box)

-- force a thunk after a substitution up to hnf. cannot pattern match on values otherwise
-- TODO: during forcing and in eval - do we delete the substituted meta from the ctx and return a new one?
force :: ElabCtx -> Value -> Value
force ctx (VFlex m sp _)
  | Substituted v <- get_free_status_partial ctx m =
      --       trace ("forcing " <> show_val ctx (VFlex m sp)) $
      force ctx (value_app_spine ctx v sp)
force _ v = v

deep_force :: ElabCtx -> Value -> Value
deep_force ctx (VFlex m sp _)
  | Substituted v <- get_free_status_partial ctx m = deep_force ctx (value_app_spine ctx v sp)
deep_force ctx (VRigid r sp a) = VRigid r (fmap (deep_force ctx) sp) a
deep_force ctx (VLam s va vb) = VLam s (deep_force ctx va) $ deep_force ctx . vb
deep_force ctx (VPi s v vb) = VPi s (deep_force ctx v) $ deep_force ctx . vb
deep_force _ v = v

-- where the computation happens
value_app :: ElabCtx -> Value -> Value -> Value
value_app _ (VLam _ _ body) v = body v
value_app ctx (VFlex s spine a) v = VFlex s (spine :|> v) (ty_app ctx a v)
value_app ctx (VRigid x spine a) v = VRigid x (spine :|> v) (ty_app ctx a v)
value_app _ _ _ = error "impossible"

ty_app :: ElabCtx -> Value -> Value -> Value
ty_app ctx a t = case force ctx a of
  VPi _ _ b -> b t
  _ -> error "impossible"

-- apply single value to a spine
value_app_spine :: ElabCtx -> Value -> Spine -> Value
value_app_spine _ v Empty = v
value_app_spine ctx v (spine :|> s) = value_app ctx (value_app_spine ctx v spine) s

-- normal form evaluation
eval :: ElabCtx -> Term -> Value
eval ctx (Const v) = get_const_def_partial ctx v
eval ctx (Free m) = case get_free_status_partial ctx m of
  Substituted v -> v
  Fresh _ -> VFree m (get_free_ty_partial ctx m)
eval ctx (Bound i) = ctx.lenv !!! i
eval ctx (ALam s a body) = VLam s (eval ctx a) (\x -> eval (extend_lenv ctx x) body)
eval ctx (Pi ms t1 t2) = VPi ms (eval ctx t1) (\x -> eval (extend_lenv ctx x) t2)
eval ctx (e1 :@ e2) = value_app ctx (eval ctx e1) (eval ctx e2)
eval _ (Sort s) = VSort s

quote :: ElabCtx -> Value -> Term
quote ctx v = case force ctx v of
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
    free_in :: Idx -> Term -> Bool
    free_in i (ALam _ a b) = free_in i a || free_in (i + 1) b
    free_in i (Pi _ t1 t2) = free_in i t1 || free_in (i + 1) t2
    free_in i (t1 :@ t2) = free_in i t1 || free_in i t2
    free_in i (Bound i') = i == i'
    free_in _ _ = False
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
debug_print = False
tc_trace :: [String] -> Tc ()
tc_trace ss =
  when debug_print $ trace ("TRACE " <> unwords ss) $ () `seq` pure ()
tc_trace2 :: [String] -> Tc ()
tc_trace2 ss =
  trace ("TRACE2 " <> unwords ss) $ () `seq` pure ()

mk_ctx :: SourcePos -> [Raw] -> Tc ElabCtx
mk_ctx pos = build_ctx (ElabCtx [] [] 0 [] IntMap.empty (0, "") pos)

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
infer ctx e = report ctx $ "unable to infer type for " <> show e

-- the context is just for pretty printing
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
  unless (abe_conv ctx vty_want vty_have) $
    report ctx $
      "expected type " <> show_val ctx vty_want <> " - got " <> show_val ctx vty_have
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
abe_conv :: ElabCtx -> Value -> Value -> Bool
abe_conv ctx = go (-1)
  where
    go :: Lvl -> Value -> Value -> Bool
    go _ (VSort s1) (VSort s2) = s1 == s2
    go l (VLam _ a b1) (VLam _ _ b2) = go (l - 1) (b1 $ VBound l a) (b2 $ VBound l a)
    go l (VFlex s1 sp1 _) (VFlex s2 sp2 _) = s1 == s2 && go_spine l sp1 sp2
    go l (VRigid x1 sp1 _) (VRigid x2 sp2 _) = x1 == x2 && go_spine l sp1 sp2
    go l (VPi _ a1 b1) (VPi _ a2 b2) = go l a1 a2 && go (l - 1) (b1 $ VBound l a1) (b2 $ VBound l a1)
    -- syntax-directed eta equality cases
    go l v (VLam _ a b) = go (l - 1) (value_app ctx v $ VBound l a) (b $ VBound l a)
    go l (VLam _ a b) v = go (l - 1) (b $ VBound l a) (value_app ctx v $ VBound l a)
    go _ _ _ = False
    go_spine :: Lvl -> Spine -> Spine -> Bool
    go_spine _ Empty Empty = True
    go_spine l (spine1 :|> sp1) (spine2 :|> sp2) =
      go l sp1 sp2 && go_spine l spine1 spine2
    go_spine _ _ _ = False

instance Show Sorts where
  show Star = "*"
  show Box = "□"

instance Show Term where
  showsPrec = pp_term []

-- makes ghc Show show unicode strings
instance {-# OVERLAPPING #-} Show String where
  show x = '"' : x <> "\""

print_tyannot :: Bool
print_tyannot = False

pp_term :: [String] -> Int -> Term -> ShowS
pp_term ns ep t = case t of
  Const (Name s) -> (const_typeset s <>)
  Free (Metavar m) -> ("?" <>) . (show m <>)
  Bound (Idx i) -> if i < List.genericLength ns then ((ns `List.genericIndex` i) <>) else (show i <>)
  Pi "" a b -> par ep pi_p $ pp_term ns app_p a . (" -> " <>) . pp_term ("" : ns) pi_p b
  Pi (Name s) a b ->
    par ep pi_p $
      ("forall " <>)
        . showParen (pi_again b) ((s <>) . (":" <>) . pp_term ns lam_p a)
        . go_pi (s : ns) b
    where
      go_pi nss (Pi (Name x) a' b')
        | x /= "" =
            (" " <>) . showParen True ((x <>) . (":" <>) . pp_term nss lam_p a') . go_pi (x : nss) b'
      go_pi nss e' = (". " <>) . pp_term nss pi_p e'
  e1 :@ e2 -> par ep app_p $ pp_term ns app_p e1 . (" " <>) . pp_term ns atom_p e2
  Sort s -> (show s <>)
  ALam (Name s) ty e -> par ep lam_p $ ("λ " <>) . (s <>) . pp_tyannot ty . go_alam (s : ns) e
    where
      go_alam nss (ALam (Name s') t' e') = (" " <>) . (s' <>) . pp_tyannot t' . go_alam (s' : nss) e'
      go_alam nss e' = (". " <>) . pp_term nss lam_p e'
      pp_tyannot a = if print_tyannot then (":" <>) . pp_term ns lam_p a else id
  where
    par :: Int -> Int -> ShowS -> ShowS
    par enclosing_p p = showParen (p < enclosing_p)
    pi_again :: Term -> Bool
    pi_again (Pi _ _ _) = True
    pi_again _ = False
    (atom_p, app_p, pi_p, lam_p) = (3, 2, 1, 0)
    const_typeset :: String -> String
    const_typeset s =
      Console.setSGRCode [Console.SetUnderlining Console.SingleUnderline]
        <> s
        <> Console.setSGRCode [Console.SetUnderlining Console.NoUnderline]

show_val :: ElabCtx -> Value -> String
show_val ctx = show_term ctx . quote ctx

-- TODO: explain why this is used instead of just the Show instance
show_term :: ElabCtx -> Term -> String
show_term ctx t = pp_term names 0 t ""
  where
    Ctx ct = ctx.tenv
    names = fmap (\(Name s, _) -> s) ct

pp_metastatus :: ElabCtx -> MetaStatus -> String
pp_metastatus _ (Fresh from) = show from
pp_metastatus ctx (Substituted v) = "Substituted " <> show_val ctx v

pp_substitutions :: ElabCtx -> Substitutions -> String
pp_substitutions ctx =
  IntMap.foldMapWithKey
    \key (val, status) ->
      "\t?"
        <> show key
        <> " : "
        <> show_val ctx val
        <> " -- "
        <> pp_metastatus ctx status
        <> "\n"

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

---

type Parser = Parsec Void String

debug_nosrcpos = False

with_pos :: Parser Raw -> Parser Raw
with_pos p = if debug_nosrcpos then p else RSrcPos <$> getSourcePos <*> p

whitespace :: Parser ()
whitespace = L.space C.space1 (L.skipLineComment "--") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme whitespace

symbol :: String -> Parser String
symbol = L.symbol whitespace

integer :: Parser Int
integer = lexeme L.decimal

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

semi :: Parser String
semi = symbol ";"

p_arr :: Parser String
p_arr = symbol "→" <|> symbol "->"

ident_chars :: Char -> Bool
ident_chars c = isLowerCase c || isUpperCase c || c `elem` special_chars
  where
    special_chars :: [Char] = ['_', '\'', '∀', '∃']

reserved_keywords :: [String]
reserved_keywords = ["let", "const", "free", "forall", "λ", "_lam", "_pi", "_sort"]

p_ident :: Parser Name
p_ident = do
  x <- takeWhile1P Nothing ident_chars
  guard (x `notElem` reserved_keywords)
  Name <$> (x <$ whitespace)

p_meta :: Parser Metavar
p_meta = do
  x :: Int <- integer
  pure $ Metavar x

p_let, p_clet, p_pi, p_lam, p_flet :: Parser Raw
p_let = do
  symbol "let"
  x <- p_ident
  symbol ":"
  a <- p_raw
  symbol "="
  t <- p_raw
  pure $ RLet x a t
p_clet = do
  symbol "const"
  x <- p_ident
  symbol ":"
  a <- p_raw
  pure $ RCLet x a
p_flet = do
  symbol "free"
  x <- p_meta
  symbol ":"
  a <- p_raw
  pure $ RFLet x a
p_pi = do
  symbol "forall"
  decls <- some (parens p_forall_decl <|> p_forall_decl)
  symbol "."
  b <- p_raw
  -- right associative
  pure $ foldr (uncurry RPi) b decls
p_lam = do
  symbol "λ" <|> symbol "\\"
  xs <- some p_ident
  symbol "."
  b <- p_raw
  -- also "right associative"
  pure $ foldr RLam b xs

p_atom, p_apps :: Parser Raw
p_atom = (RVar <$> p_ident) <|> p_freeref <|> p_star <|> parens p_raw
  where
    p_star = RStar <$ symbol "*"
    p_freeref = do
      symbol "?"
      x <- p_meta
      pure $ RFree x
-- left associative
p_apps = foldl1 RApp <$> some p_atom

p_forall_decl :: Parser (Name, Raw)
p_forall_decl = do
  x <- p_ident
  symbol ":"
  a <- p_raw
  pure (x, a)

p_arr_or_apps :: Parser Raw
p_arr_or_apps = do
  sp <- p_apps
  o <- optional p_arr
  case o of
    Nothing -> pure sp
    Just _ -> RPi "" sp <$> p_raw

p_raw :: Parser Raw
p_raw = with_pos $ choice ([p_let, p_clet, p_flet, p_lam, p_pi, p_arr_or_apps] :: [Parser Raw])

p_src :: Parser [Raw]
p_src = whitespace *> p_raw `sepEndBy` semi <* eof

-- mimic the megaparsec pretty printing in terms of appearance
-- massive hack, because we don't want to complicate the error type
display_err :: String -> String -> String
display_err fileconts errstr =
  let
    (sourcepos, msg) = break (== '\n') errstr
    sourcepos' = tail . filter (not . null) . split ':' $ sourcepos
    (lineno, colno) = (head sourcepos', last sourcepos')
    (lineno', colno') :: (Int, Int) = (read lineno, read colno)
    lpad = fmap (const ' ') lineno
  in
    printf "%s\n" sourcepos
      <> printf "%s |\n" lpad
      <> printf "%s | %s\n" lineno (lines fileconts !! (lineno' - 1))
      <> printf "%s | %s" lpad (replicate (colno' - 1) ' ' <> "^")
      <> printf "%s\n" msg
  where
    split :: Eq a => a -> [a] -> [[a]]
    split c xs = case break (== c) xs of
      (ls, []) -> [ls]
      (ls, _ : rs) -> ls : split c rs

append_parse_tc_toplvl :: String -> ElabCtx -> String -> ElabCtx
append_parse_tc_toplvl filename ctx contents =
  case parse p_src filename contents of
    Left e -> do
      error $ errorBundlePretty e
    Right rs -> do
      let ctx' = grow_ctx (initialPos filename) ctx rs
      case runTC ctx' of
        Left e -> error $ display_err contents e
        Right r -> r

parse_tc_toplvl :: String -> String -> ElabCtx
parse_tc_toplvl filename = append_parse_tc_toplvl filename empty_ctx

append_input_str :: ElabCtx -> String -> ElabCtx
append_input_str = append_parse_tc_toplvl "input"

input_str :: String -> ElabCtx
input_str = parse_tc_toplvl "input"

append_input_file :: ElabCtx -> String -> IO ElabCtx
append_input_file ctx filename = do
  contents <- readFile filename
  pure $ append_parse_tc_toplvl filename ctx contents

input_file :: String -> IO ElabCtx
input_file filename = do
  contents <- readFile filename
  pure $ parse_tc_toplvl filename contents
