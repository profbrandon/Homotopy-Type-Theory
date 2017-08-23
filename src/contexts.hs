
module Contexts
  ( Ctx
  , empty
  , shiftBindings
  , pushBinding
  , findBind
  )
where

newtype Ctx a = Ctx [(Int, a)]

empty :: Ctx a
empty = Ctx []

shiftBindings :: Int -> Ctx a -> Ctx a
shiftBindings n (Ctx g) = Ctx $ map (\(i, a) -> (i + n, a)) g

pushBinding :: a -> Ctx a -> Ctx a
pushBinding a g = Ctx $ (0,a) : g' where Ctx g' = shiftBindings 1 g

findBind :: Int -> Ctx a -> Maybe a
findBind n (Ctx g) = n `lookup` g