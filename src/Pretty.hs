module Pretty where

import qualified Data.List as List
import qualified System.Console.ANSI as Console
import Text.Printf
import Text.Show.Functions ()

import Core

deriving instance Show Value
deriving instance Show MetaStatus

instance Show Sorts where
  show Star = "*"
  show Box = "□"

instance Show Term where
  showsPrec = pp_term []

-- makes ghc Show show unicode strings
instance {-# OVERLAPPING #-} Show String where
  show x = '"' : x <> "\""

-- does not recurse into non-pis for exotic types
un_pi :: Term -> Term
un_pi (Pi s a b) | s /= "" && not (0 `free_in` b) = Pi "" (un_pi a) (un_pi b)
un_pi (Pi "" a b) = Pi "" (un_pi a) (un_pi b)
un_pi t = t

print_tyannot :: Bool
print_tyannot = False

-- names are used for globals
show_term :: ElabCtx -> Term -> String
show_term ctx t = pp_term names 0 t ""
  where
    Ctx ct = ctx.tenv
    names = fmap (\(Name s, _) -> s) ct

pp_term :: [String] -> Int -> Term -> ShowS
pp_term ns ep t = case t of
  Const (Name s) -> (const_typeset s <>)
  Free (Metavar m) -> ("?" <>) . (show m <>)
  Bound (Idx i) -> if i < List.genericLength ns then ((ns `List.genericIndex` i) <>) else (show i <>)
  Pi y a'' b'' -> case un_pi (Pi y a'' b'') of
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
    _ -> error "impossible"
  e1 :@ e2 -> par ep app_p $ pp_term ns app_p e1 . (" " <>) . pp_term ns atom_p e2
  Sort s -> (show s <>)
  ALam (Name s) ty e -> par ep lam_p $ ("λ " <>) . showParen (alam_again e) (pp_opt_tyannot ns s ty) . go_alam (s : ns) e
    where
      go_alam nss (ALam (Name s') t' e') = (" " <>) . showParen print_tyannot (pp_opt_tyannot nss s' t') . go_alam (s' : nss) e'
      go_alam nss e' = (". " <>) . pp_term nss lam_p e'
      pp_opt_tyannot nss x a = if print_tyannot then (x <>) . (":" <>) . pp_term nss lam_p a else (x <>)
  where
    par :: Int -> Int -> ShowS -> ShowS
    par enclosing_p p = showParen (p < enclosing_p)
    pi_again, alam_again :: Term -> Bool
    pi_again (Pi _ _ _) = True
    pi_again _ = False
    alam_again (ALam _ _ _) = print_tyannot
    alam_again _ = False
    (atom_p, app_p, pi_p, lam_p) = (3, 2, 1, 0)
    const_typeset :: String -> String
    const_typeset s =
      Console.setSGRCode [Console.SetUnderlining Console.SingleUnderline]
        <> s
        <> Console.setSGRCode [Console.SetUnderlining Console.NoUnderline]

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
