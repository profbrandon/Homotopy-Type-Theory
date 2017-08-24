
module Typing 
  (typeof)
where

import Contexts (empty, pushBinding, findBind)
import Fundamental (Wit(..), Type(..), Context, pushWBinding, cvrtSucc)
import Substitution (shiftwT, shiftw, subwwT)

data Error = UnboundWitVar      Int
           | AnnotationMismatch Type Type
           | ParamTypeMismatch  Type Type
           | MissingPiType      Type
           | MissingNatType     Type
           | ExpectedNatToVect

instance Show Error where
  show (UnboundWitVar i)        = "unbound witness variable indexed by " ++ show i
  show (AnnotationMismatch a b) = "type mismatch in annotation. Prescribed type was " ++ show a ++ ", but real type was " ++ show b
  show (ParamTypeMismatch a b)  = "type mismatch in pi type. Expected type " ++ show a ++ ", but recieved type " ++ show b
  show (MissingPiType t)        = "Expected type of the form Pi(x:T). T, but recieved type " ++ show t
  show (MissingNatType t)       = "Expected a value of type Natural, but recieved one of type " ++ show t
  show (ExpectedNatToVect)      = "Expected a value of type Natural in vector"

typeof :: Wit -> Either Error Type
typeof = typeof0 (empty,empty)

typeof0 :: Context -> Wit -> Either Error Type
typeof0 g (WVar i) = 
  case i `findBind` (fst g) of
    Nothing    -> Left $ UnboundWitVar i
    Just (_,t) -> return t
typeof0 g (WAnn w t) = do
  tw <- typeof0 g w
  if t == tw then return t else Left $ AnnotationMismatch t tw
typeof0 g (WAbs s t w) = do
  tw <- typeof0 g' w 
  return $ WitPiTyp s t tw
  where g' = (pushWBinding (s,t) (fst g), snd g)
typeof0 g (WApp a b) = do
  ta <- typeof0 g a
  tb <- typeof0 g b
  case ta of
    WitPiTyp _ t1 t2 -> 
      if t1 == tb then return $ shiftwT (-1) 0 (subwwT 0 (shiftw 1 0 b) t2) else Left $ ParamTypeMismatch t1 tb
    t                -> Left $ MissingPiType t 
typeof0 g (WVect l) = do
  b <- allNat l
  if b then return $ VectCon (cvrtSucc $ length l) else Left ExpectedNatToVect
  where allNat [] = return True
        allNat (k:ks) = do
          tk <- typeof0 g k
          tks <- allNat ks
          return $ tk == NatTyp && tks
typeof0 g (WSucc w) = do
  tw <- typeof0 g w
  if tw == NatTyp then return NatTyp else Left $ MissingNatType tw
typeof0 _ WUnit = return UnitTyp
typeof0 _ WZero = return NatTyp