module Core where

import Control.Monad.Except
import Data.IntMap (IntMap)
import Data.Sequence (Seq (..))
import Data.String (IsString)
import GHC.Exts (IsList)
import Text.Megaparsec (SourcePos)

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
  | RALam Name Raw Raw
  | RPi Name Raw Raw
  | RStar
  | RFree Metavar -- ?f
  | RLet Name Raw Raw -- let x:a = t
  | RCLet Name Raw -- const x:a
  | RFLet Metavar Raw -- free x:a
  | RSrcPos SourcePos Raw -- for error reporting
  -- formula
  --   (x = y) ∧ (y ≠ z ∨ z = \(t:Bool).t);
  | RForm [[Literal Raw]]
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

pattern VBound :: Lvl -> Value -> Value
pattern VBound x a = VRigid (Left x) [] a

-- proxy value (for a constant)
pattern VConst :: Name -> Value -> Value
pattern VConst x a = VRigid (Right x) [] a
pattern VFree :: Metavar -> Value -> Value
pattern VFree m a = VFlex m [] a

data EmergedFrom = Elim | Ident | Dummy | Skolem | User | Fluidsup | Other
  deriving (Show, Eq)
data MetaStatus = Substituted Value | Fresh EmergedFrom

type Substitution = IntMap (Value, MetaStatus)

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
  , metactx :: Substitution
  , dbg_unif :: (Integer, String)
  , srcpos :: SourcePos
  , problem :: Maybe Formset
  }

data Literal a = Pos (a, a) | Neg (a, a)
  deriving (Traversable, Foldable, Functor, Show)

lfst, lsnd :: Literal a -> a
lfst (Pos (x, _)) = x
lfst (Neg (x, _)) = x
lsnd (Pos (_, y)) = y
lsnd (Neg (_, y)) = y

-- plain lists are fine, since clause sets are commonly not large
-- duplicates should be deleted
newtype Clause = Cl [Literal Value]

-- we use plain lists here too for now, although it's quite inefficient
type Formset = [Clause]

newtype Ctx a = Ctx [(Name, a)]
  deriving (IsList, Semigroup, Monoid, Show) via [(Name, a)]
  deriving (Functor)

extend_ctx :: (Name, a) -> Ctx a -> Ctx a
extend_ctx (s, t) (Ctx e) = Ctx $ (s, t) : e

lookup_ctx :: Ctx a -> Name -> Either String a
lookup_ctx (Ctx r) s = case lookup s r of
  Just t -> pure t
  Nothing -> throwError $ "cannot find variable " <> show s

lookup_ctx_partial :: Ctx a -> Name -> a
lookup_ctx_partial c = either error id . lookup_ctx c

lookup_ctx_idx :: Ctx a -> Name -> Either String (Idx, a)
lookup_ctx_idx (Ctx r) key = go 0 r
  where
    go _ [] = throwError $ "cannot find variable " <> show key
    go i ((s, x) : sxs)
      | key == s = pure $ (i, x)
      | otherwise = go (i + 1) sxs

-- needed in pretty printing and η-reduction
free_in :: Idx -> Term -> Bool
free_in i (ALam _ a b) = free_in i a || free_in (i + 1) b
free_in i (Pi _ t1 t2) = free_in i t1 || free_in (i + 1) t2
free_in i (t1 :@ t2) = free_in i t1 || free_in i t2
free_in i (Bound i') = i == i'
free_in _ _ = False
