
module Typing where

import Utils

data Error = UnboundWitVar String

type Constraints = [(Type,Type)]

instance Show Error where
  show (UnboundWitVar n) = "unbound witness variable `" ++ n ++ "`"

typeof :: Wit -> Either Error Type
typeof w = 
  case typeof0 [] empty w of
    Left e      -> Left e
    Right (t,_) -> Right t

typeof0 :: Constraints -> Context -> Wit -> Either Error (Type, Constraints)
typeof0 _ g (WitVar n) = 
  case n `lookup` (fst g) of
    Nothing -> Left $ UnboundWitVar n
    Just t  -> return (t, [])
typeof0 c g (WitDef ds w) = undefined 