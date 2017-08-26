
module Parser where

import Text.Parsec ((<|>), (<?>), many, parse, parserZero, try)
import Text.Parsec.String (Parser)
import Text.Parsec.Char (alphaNum, char, lower, spaces, string, upper)

import Contexts (Ctx(..), empty)
import Fundamental (Wit(..), Type(..), Context, pushWBinding)

-- Witness Parsing

wexpr :: Context -> Parser Wit
wexpr g = do
  w <- witness g
  wapp g w

witness :: Context -> Parser Wit
witness g =
  (   (try $ wvar g)
  <|> (try $ wlet g)
  <|> (try $ wlambda g)
  <|> (try $ typAnnot g))

wapp :: Context -> Wit -> Parser Wit
wapp g w1 = 
  (try $ do w2 <- witness g; wapp g $ WApp w1 w2)
  <|> return w1

wvar :: Context -> Parser Wit
wvar g = do
  n <- witId
  let (Ctx w,_) = g
      m'        = foldl (\m (i,(s,_)) -> if s == n then Just i else m) Nothing w
  case m' of
    Nothing -> parserZero <?> ("Unbound witness variable '" ++ n ++  "' in parse")
    Just i  -> return $ WVar i

typAnnot :: Context -> Parser Wit
typAnnot g = do
  w <- witness g; spaces
  t <- typ g; spaces
  return $ WAnn w t

wlet :: Context -> Parser Wit
wlet g = do
  string "let"; spaces
  n <- witId; spaces; char ':'; spaces
  t <- typ g; spaces; string "in"; spaces
  let g' = (pushWBinding (n,t) (fst g), snd g)
  w <- witness g'; spaces
  return $ WLet n t w

wlambda :: Context -> Parser Wit
wlambda g = do
  string "lambda"; spaces; char '('; spaces
  s <- witId; spaces; char ':'; spaces
  t <- typ g; spaces; char ')'; spaces; char '.'; spaces
  let g' = (pushWBinding (s,t) (fst g), snd g)
  w <- witness g'; spaces
  return $ WAbs s t w

witId :: Parser String
witId = do
  c <- lower
  s <- many (alphaNum <|> char '\'' <|> char '_')
  return $ c:s

-- Type Parsing

typ :: Context -> Parser Type
typ g = tvar g

tvar :: Context -> Parser Type
tvar g = do
  n <- typId
  let (_,Ctx t) = g
      m'        = foldl (\m (i,s) -> if s == n then Just i else m) Nothing t
  case m' of 
    Nothing -> return $ TypConst n
    Just i  -> return $ TypVar i

typId :: Parser String 
typId = do
  c <- upper
  s <- many (alphaNum <|> char '\'' <|> char '_')
  return $ c:s