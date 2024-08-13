module Parse where

import Control.Monad
import Data.Char
import Data.Void
import Text.Megaparsec hiding (Stream)
import qualified Text.Megaparsec.Char as C (space1)
import qualified Text.Megaparsec.Char.Lexer as L

import Core

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

p_let, p_clet, p_pi, p_lam, p_alam, p_flet :: Parser Raw
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
  args <- some (parens p_typed_args <|> p_typed_args)
  symbol "."
  b <- p_raw
  -- right associative
  pure $ foldr (uncurry RPi) b args
p_lam = do
  symbol "λ" <|> symbol "\\"
  xs <- some p_ident
  symbol "."
  b <- p_raw
  -- also "right associative"
  pure $ foldr RLam b xs
p_alam = do
  symbol "λ" <|> symbol "\\"
  args <- some (parens p_typed_args <|> p_typed_args)
  symbol "."
  b <- p_raw
  pure $ foldr (uncurry RALam) b args

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

p_typed_args :: Parser (Name, Raw)
p_typed_args = do
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
p_raw = with_pos $ choice ([p_let, p_clet, p_flet, try p_alam, p_lam, p_pi, p_arr_or_apps] :: [Parser Raw])

p_src :: Parser [Raw]
p_src = whitespace *> p_raw `sepEndBy` semi <* eof

parse_raw :: String -> String -> Either (ParseErrorBundle String Void) [Raw]
parse_raw = parse p_src
