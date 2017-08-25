
module Fundamental
  ( Wit(..)
  , Type(..)
  , Context
  , pushWBinding
  )
where

import Contexts (Ctx(..), empty, pushBinding, findBind)

{- * Note, I chose witness instead of term because of the fact that type also starts with t,
 -   and the fact that a : A can be read as "'a' is a witness of the proposition 'A'".
 -}

data Wit = WVar  Int             -- Variables:                       x
         | WAnn  Wit    Type     -- Annotations:                     w : T
         | WLet  String Type Wit -- Let Type-Binding:                let n : T in w
         | WAbs  String Type Wit -- Witness Dependent Abstractions:  λ x : T . w
         | WApp  Wit    Wit      -- Witness Dependent Application:   w w
         -- Primitive Witnesses
         | WitC  String          -- Witness Constant:                c
         deriving Eq

data Type = TypVar   Int                -- Type Variable:              U
          | WitPiTyp String Type Type   -- Witness Dependent Pi-Type:  Π(x : T). T
          -- Conctrete Types
          | TypC     String             -- Type Constant:              C
          deriving Eq

instance Show Wit where
  show = showWit (empty,empty)

instance Show Type where
  show = showType (empty,empty)

type WContext = Ctx (String, Type)   -- Witness Context
type TContext = Ctx String           -- Type Context
type Context  = (WContext, TContext)

-- pushWBinding is different from pushBinding because it shifts all witness variables in the type bindings by 1

pushWBinding :: (String,Type) -> WContext -> WContext
pushWBinding p g = Ctx $ map (\(i,(s,t)) -> (i,(s, shiftwT 1 t))) l
  where
    Ctx l = pushBinding p g
    shiftw i (WVar j)     = WVar $ i + j
    shiftw i (WAnn w t)   = WAnn (shiftw i w) (shiftwT i t)
    shiftw i (WAbs s t w) = WAbs s (shiftwT i t) (shiftw i w)
    shiftw i (WApp a b)   = WApp (shiftw i a) (shiftw i b)
    shiftw _ w            = w
    shiftwT i (WitPiTyp s a b) = WitPiTyp s (shiftwT i a) (shiftwT i b)
    shiftwT _ w                = w

-- closedWit and closedTyp determine wheter a witness or a type has free variables, respectively.

closedWit :: Wit -> Bool
closedWit = closedWit0 (empty,empty)

closedWit0 :: Context -> Wit -> Bool
closedWit0 g (WVar i)     = case i `findBind` (fst g) of Nothing -> False; Just _ -> True
closedWit0 g (WAnn w t)   = closedWit0 g w && closedTyp0 g t
closedWit0 g (WAbs s t w) = closedWit0 g' w && closedTyp0 g t where g' = (pushWBinding (s,t) (fst g), snd g)
closedWit0 g (WApp a b)   = closedWit0 g a && closedWit0 g b
closedWit0 _ _            = True

closedTyp :: Type -> Bool
closedTyp = closedTyp0 (empty,empty)

closedTyp0 :: Context -> Type -> Bool
closedTyp0 g (WitPiTyp s a b) = closedTyp0 g a && closedTyp0 g' b where g' = (pushWBinding (s,a) (fst g), snd g)
closedTyp0 g (TypVar i)       = case i `findBind` (snd g) of Nothing -> False; Just _ -> True
closedTyp0 _ _                = True

-- hasWVar and hasTWVar are used to determine if a dependent type is constant.
  -- If the dependent type is constant than it is printed in simpliefied notation.

hasWVar :: Int -> Wit -> Bool
hasWVar i (WVar j)     = i == j
hasWVar i (WAnn w t)   = hasWVar i w || hasTWVar i t
hasWVar i (WAbs s t w) = hasTWVar (i + 1) t || hasWVar (i + 1) w
hasWVar i (WApp a b)   = hasWVar i a || hasWVar i b
hasWVar _ _            = False

hasTWVar :: Int -> Type -> Bool
hasTWVar i (WitPiTyp s a b) = hasTWVar i a || hasTWVar (i + 1) b
hasTWVar _ _                = False

-- showWit and showTyp are used to make Wit and Type members of the Show typeclass
  -- showNumber and cvrtNum show natural numbers
  -- tOptParen and wOptParen are used if parenthesis are optional depending on the argument

showWit :: Context -> Wit -> String
showWit g (WVar i) = 
  case i `findBind` (fst g) of
    Nothing    -> "(Witness Variable: " ++ show i ++ ")"
    Just (s,_) -> s
showWit g (WAnn w t)   = wOptParen g w ++ ":" ++ showType g t
showWit g (WLet n t w) = "let " ++ n ++ ":" ++ showType g t ++ " in " ++ showWit g' w where g' = (pushWBinding (n,t) (fst g), snd g)
showWit g (WAbs s t w) = "Lambda(" ++ s ++ ":" ++ showType g t ++ "). " ++ showWit g' w where g' = (pushWBinding (s,t) (fst g), snd g)
showWit g (WApp a b)   = wOptParen g a ++ " " ++ wOptParen g b
showWit _ (WitC n)     = n

showType :: Context -> Type -> String
showType g (TypVar i) =
  case i `findBind` (snd g) of
    Nothing -> "(Type Variable: " ++ show i ++ ")"
    Just s  -> s
showType g (WitPiTyp s a b) 
  | hasTWVar 0 b = "Pi(" ++ s ++ ":" ++ showType g a ++ "). " ++ showType g' b 
  | otherwise    = tOptParen g a ++ " -> " ++ showType g' b
  where g' = (pushWBinding (s,a) (fst g), snd g)
showType _ (TypC n)    = n

tOptParen :: Context -> Type -> String
tOptParen g (WitPiTyp s a b) = "(" ++ showType g (WitPiTyp s a b) ++ ")"
tOptParen g t                = showType g t

wOptParen :: Context -> Wit -> String
wOptParen g (WAnn w t)   = "(" ++ showWit g (WAnn w t) ++ ")"
wOptParen g (WAbs s t w) = "(" ++ showWit g (WAbs s t w) ++ ")"
wOptParen g (WApp a b)   = "(" ++ showWit g (WApp a b) ++ ")"
wOptParen g t            = showWit g t