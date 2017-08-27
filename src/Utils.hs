
module Utils
  ( Wit(..)
  , Type(..)
  , Family(..)
  , Def(..)
  , WitPat(..)
  , TypPat(..)
  , ArgP(..)
  , Context(..)
  , empty
  , pushWBinding
  , pushTBinding
  , hasWitVar
  , hasTypVar
  )
where

import Data.Maybe (isJust)

{- * Note, I chose witness instead of term because of the fact that type also starts with t,
 -   and the fact that a : A can be read as "'a' is a witness of the proposition 'A'".
 -}

data Wit = WitVar String                -- Variables:                     x
         | WitDef [Def]  Wit            -- Definition Expression:         define defs in w 

data Type = TypVar   String             -- Type Variable:                 U
          | WitPiTyp String Type Type   -- Witness Dependent Pi-Type:     Π(x:T). T
          | TypWApp  Type   Wit         -- Type-Witness Application:      T w

data Family = Universe                  -- Universe Family:               @
            | ArrFam Type Family        -- Arrow Family:                  T → F

data Def = WitDefJudge WitPat Wit       -- Witness Definition Judgement:  witpat :≡ w
         | WitTypJudge WitPat Type      -- Witness Type Judgement:        witpat : T
         | TypDefJudge TypPat Type      -- Type Definition Judgement:     typpat :≡ T
         | TypFamJudge TypPat Family    -- Type Family Judgement:         typpat : F

data WitPat = WitVal String             -- Witness Value:                 c
            | FApp   WitPat    ArgP     -- Function Application Pattern:  w ap

data TypPat = TypVal String             -- Type Value:                    C
            | OApp   TypPat    ArgP     -- Operator Application Pattern:  T ap

type ArgP = Either WitPat TypPat        -- Argument Pattern:              wp | tp

{- Contexts consist of both a witness context and a type context 
 -   empty represents an empty context
 -   pushWBinding pushes a witness-type pair onto the context
 -   pushTBinding pushes a type-family pair onto the context
 -}

type WContext = [(String, Type)]
type TContext = [(String, Family)]
type Context  = (WContext, TContext)

empty = ([],[])

pushWBinding p (wg,tg) = (p:wg,tg)

pushTBinding p (wg,tg) = (wg,p:tg)

hasWitVar :: String -> Context -> Bool
hasWitVar n (wg,_) = isJust (n `lookup` wg)

hasTypVar :: String -> Context -> Bool
hasTypVar n (_,tg) = isJust (n `lookup` tg)