{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Superpos where

import qualified Data.List as List

import Elab

data Literal = Pos (Value, Value) | Neg (Value, Value)
pattern a :≉ b = Neg (a, b)
pattern a :≈ b = Pos (a, b)
infix 4 :≉
infix 4 :≈

-- unoriented equality for literals
eq_lit :: ElabCtx -> Literal -> Literal -> Bool
eq_lit ctx l r = case (l, r) of
  (Pos l', Pos r') -> go l' r'
  (Neg l', Neg r') -> go l' r'
  (_, _) -> False
  where
    (c1, c2) `go` (d1, d2) = c1 `cmp` d1 && c2 `cmp` d2 || c1 `cmp` d2 && c2 `cmp` d1
    cmp = abe_conv ctx

show_lit :: ElabCtx -> Literal -> String
show_lit ctx (Pos (l, r)) = show_val ctx l <> "≈" <> show_val ctx r
show_lit ctx (Neg (l, r)) = show_val ctx l <> "≉" <> show_val ctx r

-- plain lists are fine here, since clause sets are commonly not large
-- duplicates should be deleted
newtype Clause = Cl [Literal]

show_cl :: ElabCtx -> Clause -> String
show_cl _ (Cl []) = "⊥"
show_cl ctx (Cl cs) = List.intercalate " ∨ " (show_lit ctx <$> cs)

-- we use plain lists for now, although it's quite inefficient
type Formset = [Clause]

bool_prelude :: ElabCtx
bool_prelude =
  input_str $
    unlines
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
    va = value_app bool_prelude

base_prelude :: ElabCtx
base_prelude =
  append_input_str bool_prelude $
    unlines
      [ "const funext : forall a:* b:*. (a -> b) -> (a -> b) -> a;"
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
    va = value_app base_prelude
