
module Substitution 
  ( subwww
  , subwwT
  , shiftw
  , shiftwT
  )
where

import Fundamental (Wit(..), Type(..))

shiftw :: Int -> Int -> Wit -> Wit
shiftw d c (WVar i)     = WVar $ if i < c then i else d + i
shiftw d c (WAnn w t)   = WAnn (shiftw d c w) (shiftwT d c t)
shiftw d c (WAbs s t w) = WAbs s (shiftwT d c t) (shiftw d (c + 1) w)
shiftw d c (WApp a b)   = WApp (shiftw d c a) (shiftw d c b)
shiftw d c (WSucc w)    = WSucc (shiftw d c w)
shiftw d c (WVect l)    = WVect $ map (shiftw d c) l
shiftw _ _ w            = w

shiftwT :: Int -> Int -> Type -> Type
shiftwT d c (WitPiTyp s t y) = WitPiTyp s (shiftwT d c t) (shiftwT d (c + 1) y)
shiftwT d c (VectCon w)      = VectCon $ shiftw d c w
shiftwT _ _ t                = t

subwww :: Int -> Wit -> Wit -> Wit
subwww i a (WVar j)     = if i == j then a else WVar j
subwww i a (WAnn w t)   = WAnn (subwww i a w) (subwwT i a t)
subwww i a (WAbs s t w) = WAbs s (subwwT i a t) (subwww (i + 1) (shiftw 1 0 a) w)
subwww i a (WApp w q)   = WApp (subwww i a w) (subwww i a q)
subwww i a (WSucc w)    = WSucc (subwww i a w)
subwww i a (WVect l)    = WVect $ map (subwww i a) l
subwww _ _ w            = w

subwwT :: Int -> Wit -> Type -> Type
subwwT i a (WitPiTyp s t y) = WitPiTyp s (subwwT i a t) (subwwT (i + 1) (shiftw 1 0 a) y)
subwwT i a (VectCon w)      = VectCon $ subwww i a w
subwwT _ _ t                = t