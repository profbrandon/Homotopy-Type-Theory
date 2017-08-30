
module Parser 
  (parseWit)
where

import Text.Parsec ((<|>), (<?>), many, parse, parserFail, sepBy1, try)
import Text.Parsec.String (Parser)
import Text.Parsec.Char (alphaNum, char, lower, spaces, string, upper)
import Utils
import Printing

-- Witness Parsing

parseWit = parse (wit empty) ""

wit :: Context -> Parser Wit
wit g = do
  w <- wit0 g
  wapp g w

wit0 :: Context -> Parser Wit
wit0 g = (try $ wvar g) <|> (wdef g)

wdef :: Context -> Parser Wit
wdef g = do
  string "define "; spaces
  (ds, g') <- defs g; string "in ";
  w <- wit g'
  return $ WitDef ds w

wapp :: Context -> Wit -> Parser Wit
wapp g w1 = 
  (try $ do w2 <- wit0 g; wapp g $ WitApp w1 w2) <|> (return w1)

wvar :: Context -> Parser Wit
wvar g = do
  n <- witId
  case n `lookup` (fst g) of
    Nothing -> parserFail $ "Unbound Witness Variable"
    Just _  -> return $ WitVar n

witId :: Parser String
witId = do
  c <- lower
  s <- many (alphaNum <|> char '\''); spaces
  return $ c:s

-- Type Parsing

typ :: Context -> Parser Type
typ g = do
  t1 <- (try $ do char '('; spaces; t <- typ g; char ')'; spaces; return t) <|> (typ0 g)
  arrTyp g t1

typ0 :: Context -> Parser Type
typ0 g = (try $ tvar g) <|> (witPiTyp g)

witPiTyp :: Context -> Parser Type
witPiTyp g = do
  string "Pi"; spaces; char '('; spaces
  n <- witId; char ':'; spaces
  t <- typ g; char ')'; spaces; char '.'; spaces
  let g' = pushWBinding (n,t) g
  y <- typ g'
  return $ WitPiTyp n t y

arrTyp :: Context -> Type -> Parser Type
arrTyp g t1 = 
  (try $ do
  string "->"; spaces
  t2 <- typ g
  return $ WitPiTyp "" t1 t2)
    <|> (do return t1)

tvar :: Context -> Parser Type
tvar g = do
  n <- typId
  case n `lookup` (snd g) of
    Nothing -> parserFail $ "Unbound Type Variable"
    Just _  -> return $ TypVar n

typId :: Parser String 
typId = do
  c <- upper
  s <- many (alphaNum <|> char '\''); spaces
  return $ c:s

-- Family Parsing

fam :: Context -> Parser Family
fam g = (try $ universe) <|> (arrFam g)

arrFam :: Context -> Parser Family
arrFam g = do
  t <- typ g; string "->"; spaces
  f <- fam g
  return $ ArrFam t f

universe :: Parser Family
universe = do char '@'; spaces; return Universe 

-- Definition Pattern Parsing

defs :: Context -> Parser ([Def], Context)
defs g = do
  (d, g0) <- def g
  (try $ do char ','; spaces; (ds, g1) <- defs g0; return $ (d:ds, g1))
    <|> return ([d], g0)

def :: Context -> Parser (Def, Context)
def g = 
  (      try $ wdj) 
    <|> (try $ wtj)
    <|> (try $ tdj)
    <|> tfj
  where wdj = do (wp,n,g0) <- witpat g; string ":="; spaces; w <- wit g0; return $ (WitDefJudge wp w, pushWBinding (n,TypVar "$") g)
        wtj = do (wp,n,g0) <- witpat g; char   ':';  spaces; t <- typ g0; return $ (WitTypJudge wp t, pushWBinding (n,t) g)
        tdj = do (tp,n,g0) <- typpat g; string ":="; spaces; t <- typ g0; return $ (TypDefJudge tp t, pushTBinding (n,Universe) g)
        tfj = do (tp,n,g0) <- typpat g; char   ':';  spaces; f <- fam g0; return $ (TypFamJudge tp f, pushTBinding (n,f) g)

witpat :: Context -> Parser (WitPat, String, Context)
witpat g = do
  n <- witId
  (w, g') <- fapp (WitVal n) g
  return (w, n, g')
  where fapp wp g0 = (try $ do (a,g1) <- argp g0; fapp (FApp wp a) g1) <|> (do return (wp, g0))

typpat :: Context -> Parser (TypPat, String, Context)
typpat g = do
  n <- typId
  (w, g') <- oapp (TypVal n) g
  return (w, n, g')
  where oapp wp g0 = (try $ do (a,g1) <- argp g0; oapp (OApp wp a) g1) <|> (do return (wp, g0))

argp :: Context -> Parser (ArgP, Context)
argp g =
  (    try $ do n <- witId; return $ (Left $ WitVal n, pushWBinding (n,TypVar "$") g))
  <|> (try $ do n <- typId; return $ (Right $ TypVal n, pushTBinding (n,Universe) g))
  <|> (try $ do char '('; spaces; (w,n,g) <- witpat g; char ')'; spaces; return (Left w, pushWBinding (n,TypVar "$") g))
  <|> (do char '('; spaces; (t,n,g) <- typpat g; char ')'; spaces; return (Right t, pushTBinding (n,Universe) g))


    