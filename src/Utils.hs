
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

import Data.List (union, delete)
import Data.Maybe (isJust)

{- * Note, I chose witness instead of term because of the fact that type also starts with t,
 -   and the fact that a : A can be read as "'a' is a witness of the proposition 'A'".
 -}

data Wit = WitVar    String              -- Variables:                             x
         | WitDef    [Def]  Wit          -- Definition Expression:                 define defs in w 
         | WitWitAbs String Type   Wit   -- Witness Dependent Lambda Abstraction:  λ(x:T). w
         | WitTypAbs String Family Wit   -- Type Dependent lambda Abstraction:     λ(U:F). w
         | WitWitApp Wit    Wit          -- Witness-Witness Application:           w w
         | WitTypApp Wit    Type         -- Witness-Type Application:              w T
         deriving Eq

data Type = TypVar    String             -- Type Variable:                         U
          | WitPiTyp  String Type   Type -- Witness Dependent Pi-Type:             Π(x:T). T
          | TypPiTyp  String Family Type -- Type Dependent Pi-Type:                Π(T:F). T
          deriving Eq

data Family = Universe                   -- Universe Family:                  @
            | ArrFam Type Family         -- Arrow Family:                     T → F
            deriving Eq

data Def = WitDefJudge WitPat Wit        -- Witness Definition Judgement:     wp :≡ w
         | WitTypJudge WitPat Type       -- Witness Type Judgement:           wp : T
         | TypDefJudge TypPat Type       -- Type Definition Judgement:        wp :≡ T
         | TypFamJudge TypPat Family     -- Type Family Judgement:            wp : F
         deriving Eq

data WitPat = WitVal String              -- Witness Value:                    c
            | FApp   WitPat    ArgP      -- Function Application Pattern:     w ap
            deriving Eq

data TypPat = TypVal String              -- Type Value:                       C
            | OApp   TypPat    ArgP      -- Operator Application Pattern:     T ap
            deriving Eq

type ArgP = Either WitPat TypPat         -- Argument Pattern:                 wp | tp

{- Contexts consist of both a witness context and a type context 
 -   empty represents an empty context
 -   pushWBinding pushes a witness-type pair onto the context
 -   pushTBinding pushes a type-family pair onto the context
 -}

type WContext = [(String, Type)]
type TContext = [(String, Family)]
type Context  = (WContext, TContext)

empty = ([],[])

pushWBinding p@(n,_) g@(wg,tg) 
  | hasWitVar n g = g
  | otherwise     = (p:wg,tg)

pushTBinding p@(n,_) g@(wg,tg) 
  | hasTypVar n g = g
  | otherwise     = (wg,p:tg)

hasWitVar :: String -> Context -> Bool
hasWitVar n (wg,_) = isJust (n `lookup` wg)

hasTypVar :: String -> Context -> Bool
hasTypVar n (_,tg) = isJust (n `lookup` tg)

freeTypVars :: Context -> Type -> [String]
freeTypVars g (TypVar s)        = if hasTypVar s g then [] else [s]
freeTypVars g (WitPiTyp _ t y)  = freeTypVars g y `union` freeTypVars g t
freeTypVars g (TypPiTyp s f t)  = delete s $ ffreeTypVars g f `union` freeTypVars g' t where g' = pushTBinding (s,f) g

ffreeTypVars :: Context -> Family -> [String]
ffreeTypVars _ Universe     = []
ffreeTypVars g (ArrFam t f) = freeTypVars g t `union` ffreeTypVars g f

-- Retireve all type variables in a family
ftypVars :: Family -> [String]
ftypVars Universe     = []
ftypVars (ArrFam t f) = ftypVars f `union` ttypVars t

-- Retireve all type variables in a type
ttypVars :: Type -> [String]
ttypVars (TypVar "")       = []
ttypVars (TypVar s)        = [s]
ttypVars (WitPiTyp s t y)  = ttypVars t `union` ttypVars y
ttypVars (TypPiTyp s f t)  = s:(ftypVars f `union` ttypVars t)

-- Retireve all type variables in a witness
wtypVars :: Wit -> [String]
wtypVars (WitVar _)        = []
wtypVars (WitWitAbs s t w) = s:wtypVars w `union` ttypVars t
wtypVars (WitTypAbs _ f w) = ftypVars f `union` wtypVars w
wtypVars (WitWitApp a b)   = wtypVars a `union` wtypVars b
wtypVars (WitTypApp w t)   = wtypVars w `union` ttypVars t
wtypVars (WitDef ds w)     = wtypVars w `union` dstypVars ds
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

