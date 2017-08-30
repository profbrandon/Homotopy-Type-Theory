
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
  , freeTypVars
  , wtypVars
  )
where

import Data.List (union)
import Data.Maybe (isJust)

{- * Note, I chose witness instead of term because of the fact that type also starts with t,
 -   and the fact that a : A can be read as "'a' is a witness of the proposition 'A'".
 -}

data Wit = WitVar String                -- Variables:                     x
         | WitDef [Def]  Wit            -- Definition Expression:         define defs in w 
         | WitApp Wit    Wit            -- Witness-Witness Application:   w w

data Type = TypVar   String             -- Type Variable:                 U
          | WitPiTyp String Type Type   -- Witness Dependent Pi-Type:     Π(x:T). T
          deriving Eq

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

freeTypVars :: Type -> [String]
freeTypVars (TypVar s)       = [s]
freeTypVars (WitPiTyp s t y) = freeTypVars y `union` freeTypVars t

ftypVars :: Family -> [String]
ftypVars Universe     = []
ftypVars (ArrFam t f) = ftypVars f `union` ttypVars t

ttypVars :: Type -> [String]
ttypVars (TypVar s)       = [s]
ttypVars (WitPiTyp s t y) = ttypVars t `union` ttypVars y

wtypVars :: Wit -> [String]
wtypVars (WitVar _)    = []
wtypVars (WitApp a b)  = wtypVars a `union` wtypVars b
wtypVars (WitDef ds w) = wtypVars w `union` dstypVars ds
  where dstypVars [WitDefJudge wp w] = wtypVars w `union` wptypVars wp
        dstypVars [WitTypJudge wp t] = ttypVars t `union` wptypVars wp
        dstypVars [TypDefJudge tp t] = ttypVars t `union` tptypVars tp
        dstypVars [TypFamJudge tp f] = ftypVars f `union` tptypVars tp
        dstypVars (d:ds)             = dstypVars [d] `union` dstypVars ds
        wptypVars (WitVal _)         = []
        wptypVars (FApp wp a)        = wptypVars wp `union` atypVars a
        tptypVars (TypVal s)         = [s]
        tptypVars (OApp tp a)        = tptypVars tp `union` atypVars a
        atypVars  (Left wp)          = wptypVars wp
        atypVars  (Right tp)         = tptypVars tp

