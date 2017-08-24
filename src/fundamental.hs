
module Fundamental
  ( Wit(..)
  , Type(..)
  , Context
  , pushWBinding
  , cvrtSucc
  )
where

import Contexts (Ctx(..), empty, pushBinding, findBind)

data Wit = WVar  Int             -- Variables:                       x
         | WAnn  Wit    Type     -- Annotations:                     w : T
         | WAbs  String Type Wit -- Witness Dependent Abstractions:  λ x : T . w
         | WApp  Wit    Wit      -- Witness Dependent Application:   w w
         -- Primitive Constructor Witnesses
         | WVect [Wit]           -- Vector of Natural Numbers:       <w, w, w, ...>
         -- Primitive Witnesses
         | WUnit                 -- Unit:                            *
         | WZero                 -- Zero:                            0
         | WSucc Wit             -- Successor:                       succ w
         deriving Eq

data Type = TypVar   Int                -- Type Variable:              U
          | WitPiTyp String Type Type   -- Witness Dependent Pi-Type:  Π(x : T). T 
          -- Test Constructors
          | VectCon  Wit                -- Vector Constructor:         Vector(w)
          -- Conctrete Types
          | UnitTyp                     -- Unit Type:                  1
          | NatTyp                      -- Natural Number Type:        Natural
          deriving Eq

instance Show Wit where
  show = showWit (empty,empty)

instance Show Type where
  show = showType (empty,empty)

type WContext = Ctx (String, Type)
type TContext = Ctx String

pushWBinding :: (String,Type) -> WContext -> WContext
pushWBinding p g = Ctx $ map (\(i,(s,t)) -> (i,(s, shiftwT 1 t))) l
  where
    Ctx l = pushBinding p g
    shiftw i (WVar j)     = WVar $ i + j
    shiftw i (WAnn w t)   = WAnn (shiftw i w) (shiftwT i t)
    shiftw i (WAbs s t w) = WAbs s (shiftwT i t) (shiftw i w)
    shiftw i (WApp a b)   = WApp (shiftw i a) (shiftw i b)
    shiftw i (WVect l)    = WVect $ map (shiftw i) l
    shiftw i (WSucc w)    = WSucc $ shiftw i w
    shiftw _ w            = w
    shiftwT i (WitPiTyp s a b) = WitPiTyp s (shiftwT i a) (shiftwT i b)
    shiftwT i (VectCon w)      = VectCon (shiftw i w)
    shiftwT _ w                = w

type Context = (WContext, TContext)

closedWit :: Wit -> Bool
closedWit = closedWit0 (empty,empty)

closedWit0 :: Context -> Wit -> Bool
closedWit0 g (WVar i)     = case i `findBind` (fst g) of Nothing -> False; Just _ -> True
closedWit0 g (WAnn w t)   = closedWit0 g w && closedTyp0 g t
closedWit0 g (WAbs s t w) = closedWit0 g' w && closedTyp0 g t where g' = (pushWBinding (s,t) (fst g), snd g)
closedWit0 g (WApp a b)   = closedWit0 g a && closedWit0 g b
closedWit0 g (WVect l)    = and $ map (closedWit0 g) l 
closedWit0 g (WSucc w)    = closedWit0 g w
closedWit0 _ _            = True

closedTyp :: Type -> Bool
closedTyp = closedTyp0 (empty,empty)

closedTyp0 :: Context -> Type -> Bool
closedTyp0 g (WitPiTyp s a b) = closedTyp0 g a && closedTyp0 g' b where g' = (pushWBinding (s,a) (fst g), snd g)
closedTyp0 g (VectCon w)      = closedWit0 g w
closedTyp0 g (TypVar i)       = case i `findBind` (snd g) of Nothing -> False; Just _ -> True
closedTyp0 _ _                = True

hasWVar :: Int -> Wit -> Bool
hasWVar i (WVar j)     = i == j
hasWVar i (WAnn w t)   = hasWVar i w || hasTWVar i t
hasWVar i (WAbs s t w) = hasTWVar (i + 1) t || hasWVar (i + 1) w
hasWVar i (WApp a b)   = hasWVar i a || hasWVar i b
hasWVar i (WVect l)    = or $ map (hasWVar i) l
hasWVar i (WSucc w)    = hasWVar i w
hasWVar _ _            = False

hasTWVar :: Int -> Type -> Bool
hasTWVar i (WitPiTyp s a b) = hasTWVar i a || hasTWVar (i + 1) b
hasTWVar i (VectCon w)      = hasWVar i w
hasTWVar _ _                = False

showWit :: Context -> Wit -> String
showWit g (WVar i) = 
  case i `findBind` (fst g) of
    Nothing    -> "(Witness Variable: " ++ show i ++ ")"
    Just (s,_) -> s
showWit g (WAnn w t)   = wOptParen g w ++ ":" ++ showType g t
showWit g (WAbs s t w) = "Lambda(" ++ s ++ ":" ++ showType g t ++ "). " ++ showWit g' w where g' = (pushWBinding (s,t) (fst g), snd g) 
showWit g (WApp a b)   = wOptParen g a ++ wOptParen g b
showWit g (WVect c)    = "<" ++ showComponents c ++ ">"
  where showComponents [] = ""
        showComponents [k] = showWit g k
        showComponents (k:ks) = showWit g k ++ "," ++ showComponents ks
showWit _ WUnit        = "*"
showWit _ WZero        = "0"
showWit g (WSucc w)
  | closedWit w        = showNumber (WSucc w)
  | otherwise          = "succ(" ++ showWit g w ++ ")"

showType :: Context -> Type -> String
showType g (TypVar i) =
  case i `findBind` (snd g) of
    Nothing -> "(Type Variable: " ++ show i ++ ")"
    Just s  -> s
showType g (WitPiTyp s a b) 
  | hasTWVar 0 b = "Pi(" ++ s ++ ":" ++ showType g a ++ "). " ++ showType g' b 
  | otherwise    = tOptParen g a ++ " -> " ++ showType g' b
  where g' = (pushWBinding (s,a) (fst g), snd g)
showType g (VectCon n) = "Vector(" ++ showWit g n ++ ")"
showType _ UnitTyp     = "1"
showType _ NatTyp      = "Natural"

showNumber :: Wit -> String
showNumber = show . cvrtNum

cvrtNum :: Wit -> Int
cvrtNum WZero     = 0
cvrtNum (WSucc n) = 1 + cvrtNum n
cvrtNum _         = error "non-numeric value supplied to cvrtNum"

cvrtSucc :: Int -> Wit
cvrtSucc 0 = WZero
cvrtSucc n = WSucc (cvrtSucc $ n - 1)

tOptParen :: Context -> Type -> String
tOptParen g (WitPiTyp s a b) = "(" ++ showType g (WitPiTyp s a b) ++ ")"
tOptParen g t                = showType g t

wOptParen :: Context -> Wit -> String
wOptParen g (WAnn w t)   = "(" ++ showWit g (WAnn w t) ++ ")"
wOptParen g (WAbs s t w) = "(" ++ showWit g (WAbs s t w) ++ ")"
wOptParen g (WApp a b)   = "(" ++ showWit g (WApp a b) ++ ")"
wOptParen g t            = showWit g t