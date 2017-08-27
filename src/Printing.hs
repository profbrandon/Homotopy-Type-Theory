
module Printing where

import Text.Show.Unicode

import Utils

instance Show Wit where
  show = showWit empty

instance Show Type where
  show = showType empty

instance Show Family where
  show = showFamily empty

showWit :: Context -> Wit -> String
showWit g (WitVar s) =
  case s `lookup` (fst g) of
    Nothing -> "(Unbound Witness Variable: `" ++ s ++ "`)"
    Just _  -> s
showWit g (WitDef ds w) = "define " ++ str ++ " in " ++ showWit g' w where (str,g') = handleDefs g ds

showType :: Context -> Type -> String
showType g (TypVar s) =
  case s `lookup` (snd g) of
    Nothing -> "(Unbound Type Variable: `" ++ s ++ "`)"
    Just _  -> s
showType g (WitPiTyp s t y) 
  | typHasWVar s y = "Pi(" ++ s ++ ":" ++ showType g t ++ "). " ++ showType g' y
  | otherwise      = tRightAssoc g t ++ " -> " ++ showType g' y
  where g' = pushWBinding (s,t) g
showType g (TypWApp t w) = tRightAssoc g t ++ " " ++ wLeftAssoc g w

showFamily :: Context -> Family -> String
showFamily _ Universe     = "@"
showFamily g (ArrFam t f) = showType g t ++ " -> " ++ showFamily g f

handleDefs :: Context -> [Def] -> (String, Context)
handleDefs g [d] = handleDef g d
handleDefs g (d:ds) = (s1 ++ "," ++ s2, g1) where (s1, g0) = handleDef g d; (s2, g1) = handleDefs g0 ds

handleDef :: Context -> Def -> (String, Context)
handleDef g (WitDefJudge wp w) = (s ++ " :≡ " ++ showWit g2 w, g1)    where (s, n, g2) = handleWp g wp; g1 = pushWBinding (n,TypVar "$") g
handleDef g (WitTypJudge wp t) = (s ++ " : "  ++ showType g2 t, g1)   where (s, n, g2) = handleWp g wp; g1 = pushWBinding (n,t) g
handleDef g (TypDefJudge tp t) = (s ++ " :≡ " ++ showType g2 t, g1)   where (s, n, g2) = handleTp g tp; g1 = pushTBinding (n,Universe) g
handleDef g (TypFamJudge tp f) = (s ++ " : "  ++ showFamily g2 f, g1) where (s, n, g2) = handleTp g tp; g1 = pushTBinding (n,f) g

handleWp :: Context -> WitPat -> (String, String, Context)
handleWp g (WitVal n)          = (n, n, pushWBinding (n,TypVar "$") g)
handleWp g (FApp (WitVal n) a) = (n ++ "(" ++ s ++ ")", n, g2) where (s, g2) = handleArgP g a 
handleWp g (FApp wp a)         = (s1 ++ "(" ++ s2 ++ ")", n, g3) where (s1, n, g2) = handleWp g wp; (s2, g3) = handleArgP g2 a  

handleTp :: Context -> TypPat -> (String, String, Context)
handleTp g (TypVal n)          = (n, n, pushTBinding (n,Universe) g)
handleTp g (OApp (TypVal n) a) = (n ++ "(" ++ s ++ ")", n, g2) where (s, g2) = handleArgP g a 
handleTp g (OApp tp a)         = (s1 ++ "(" ++ s2 ++ ")", n, g3) where (s1, n, g2) = handleTp g tp; (s2, g3) = handleArgP g2 a 

handleArgP :: Context -> ArgP -> (String, Context)
handleArgP g (Left wp)  = (s,g0) where (s,_,g0) = handleWp g wp
handleArgP g (Right tp) = (s,g0) where (s,_,g0) = handleTp g tp

wLeftAssoc :: Context -> Wit -> String
wLeftAssoc g w = showWit g w

wRightAssoc :: Context -> Wit -> String
wRightAssoc g w = showWit g w

tLeftAssoc :: Context -> Type -> String 
tLeftAssoc g (TypWApp t w)    = "(" ++ showType g (TypWApp t w) ++ ")"
tLeftAssoc g t                = showType g t

tRightAssoc :: Context -> Type -> String
tRightAssoc g (WitPiTyp s t y) = "(" ++ showType g (WitPiTyp s t y) ++ ")"
tRightAssoc g t                = showType g t

typHasWVar :: String -> Type -> Bool
typHasWVar n (WitPiTyp s t y) = typHasWVar n t || typHasWVar n y
typHasWVar _ _                = False