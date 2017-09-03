
module Typing where

import Utils
import Printing
import Debug.Trace (trace)

data Error = UnboundWitVar         String
           | ConstraintMismatch    Type   Type
           | ParameterTypeMismatch Type   Type
           | ExpectedWitPiTyp      Type

data CError = CMismatch Type Type

type Constraints = ([(Type,Type)], [String]) -- ([(lhs, rhs)], [tvars])    lhs = rhs

nullc :: Constraints
nullc = ([],[])

instance Show Error where
  show (UnboundWitVar n)           = "unbound witness variable `" ++ n ++ "`"
  show (ConstraintMismatch s t)    = "constraint mismatch. Attempted unification of types `" ++ show s ++ "` and `" ++ show t ++ "`"
  show (ParameterTypeMismatch t y) = "parameter type mismatch.  Expected type `" ++ show t ++ "`, but recieved type `" ++ show y ++ "`"
  show (ExpectedWitPiTyp t)        = "expected type of the form:  Pi(t:T). T; but recieved type `" ++ show t ++ "`"

typeof :: Wit -> Either Error Type
typeof w = 
  case typeof0 nullc empty w of
    Left e        -> Left e
    Right (t,c,g) -> 
      case unify c of
        Left (CMismatch s t) -> Left $ ConstraintMismatch s t
        Right subs           -> return $ subAllTTT subs t

typeof0 :: Constraints -> Context -> Wit -> Either Error (Type, Constraints, Context)
typeof0 c g (WitVar n) = -- s
  case n `lookup` (fst g) of
    Nothing -> Left $ UnboundWitVar n
    Just t  -> return (t, c, g)
typeof0 c g (WitDef ds w) = do -- define ds in w
  (c', g') <- typeDefs c g ds
  typeof0 c' g' w
typeof0 c g (WitApp w q) = do -- w q
  (tw, c1, _) <- typeof0 c g w
  (tq, c2, _) <- typeof0 c1 g q
  case tw of
    WitPiTyp _ t y -> -- w : Π(_:T). Y
      if t == tq 
        then return (y, c2, g) 
        else case t of 
          TypVar ('$':_) -> let (eqs,vars) = c2 in return (y, ((t, tq):eqs,vars), g) -- w : Π(_:$X). Y,  i.e. $X = tq
          _ -> case tq of
            TypVar ('$':_) -> let (eqs,vars) = c2 in return (y, ((t, tq):eqs,vars), g)
            _ -> Left $ ParameterTypeMismatch t tq
    TypVar ('$':_) -> let (eqs,vars) = c2; x = fresh vars in return (TypVar x, ((tw, WitPiTyp "" tq (TypVar x)):eqs,x:vars), g)
    t              -> Left $ ExpectedWitPiTyp t


-- Typing For Definition Blocks

typeDefs :: Constraints -> Context -> [Def] -> Either Error (Constraints, Context)
typeDefs c g [d]    = do 
  (c', p, _) <- typeDef c g d
  case p of
    (s, Left t)  -> let g' = pushWBinding (s,t) g in return (c', g')
    (s, Right f) -> let g' = pushTBinding (s,f) g in return (c', g')
typeDefs c g (d:ds) = do
  (c', p, _) <- typeDef c g d
  let g' = 
        case p of
          (s, Left t)  -> pushWBinding (s,t) g
          (s, Right f) -> pushTBinding (s,f) g
  typeDefs c' g' ds

typeDef :: Constraints -> Context -> Def -> Either Error (Constraints, (String, Either Type Family), Context)
typeDef c g (WitDefJudge wp w) = do
  (twp, c1, (s,t), g1) <- typeWitPat c g wp
  (tw, (eqs, vars), g2) <- typeof0 c1 g1 w
  return (((twp, tw):eqs, vars), (s,Left t), g2)
typeDef c g (WitTypJudge wp t) = do
  (twp, (eqs, vars), (s,_), g1) <- typeWitPat c g wp
  return (((twp, t):eqs, vars), (s,Left t), g1)
typeDef c g (TypFamJudge tp f) = do
  (ftp, c', (s,_), g1) <- typeTypPat c g tp
  return (c', (s,Right f), g1)

typeWitPat :: Constraints -> Context -> WitPat -> Either Error (Type, Constraints, (String, Type), Context)
typeWitPat (eqs, vars) g (WitVal s)  = 
  case s `lookup` (fst g) of
    Nothing -> do 
      let x = fresh vars; g' = pushWBinding (s,TypVar x) g 
      return (TypVar x, (eqs, x:vars), (s,TypVar x), g')
    Just t  -> return (t, (eqs, vars), (s,t), g)
typeWitPat c g (FApp wp1 (Left wp2)) = do
  (twp1, c1, p, g1) <- typeWitPat c g wp1
  (twp2, (eqs, vars), _, g2) <- typeWitPat c1 g1 wp2
  let x = fresh vars
  return (TypVar x, ((twp1,WitPiTyp "" twp2 $ TypVar x):eqs, x:vars), p, g2)

typeTypPat :: Constraints -> Context -> TypPat -> Either Error (Family, Constraints, (String, Family), Context)
typeTypPat c g (TypVal s) =
  case s `lookup` (snd g) of
    Nothing -> return (Universe, c, (s,Universe), pushTBinding (s,Universe) g)
    Just f  -> return (f, c, (s,f), g)

fresh :: [String] -> String
fresh ns = fresh0 0 
  where 
    fresh0 k = let name = "$" ++ show k
               in if name `elem` ns then fresh0 (k + 1) else name

unify :: Constraints -> Either CError [(Int, Type)]
unify (eqs, _) = unify0 eqs
  where
    unify0 [] = return []
    unify0 ((s,t):cs) = 
      if s == t
        then unify0 cs
        else case s of
          TypVar ('$':x) -> 
            case hTypVar x s t cs of
              Nothing -> hback s t cs
              Just v  -> v
          _ -> hback s t cs

    hTypVar x s t cs = if not ('$':x `elem` freeTypVars t) 
                      then case unify0 (subTTc n t cs) of
                        Left  k    -> Just $ Left k
                        Right subs -> Just $ Right $ (n, t):subs
                      else Nothing
                      where n = (read x :: Int)

    hback s t cs = 
      case t of
        TypVar ('$':x) -> 
          case hTypVar x t s cs of
            Nothing -> Left $ CMismatch s t
            Just s  -> s
        _ -> case s of
          WitPiTyp _ s1 s2 ->
            case t of
              WitPiTyp _ t1 t2 ->
                unify0 $ (s1,t1):(s2,t2):cs
              _ -> Left $ CMismatch s t 
          _ -> Left $ CMismatch s t

shiftTV :: Int -> Int -> Type -> Type
shiftTV i bnd t = shiftTV0 0
  where shiftTV0 n = if n == bnd then t else subTTT n (TypVar ('$':show (n + i))) $ shiftTV0 (n + 1)

shiftTVC :: Int -> Int -> Constraints -> Constraints
shiftTVC i bnd (eqs,vars) = (map (\(t,y) -> (shiftTV i bnd t, shiftTV i bnd y)) eqs, map (\s -> let TypVar s' = shiftTV i bnd (TypVar s) in s') vars)

subTTc :: Int -> Type -> [(Type, Type)] -> [(Type, Type)]
subTTc _ _ [] = []
subTTc i t ((y1, y2):eqs) = (subTTT i t y1, subTTT i t y2):eqs' where eqs' = subTTc i t eqs 

subTTT :: Int -> Type -> Type -> Type
subTTT i t (TypVar ('$':x)) = if i == n then t else TypVar ('$':x) where n = (read x :: Int)
subTTT i t (WitPiTyp s a b) = WitPiTyp s (subTTT i t a) (subTTT i t b)
subTTT _ _ t                = t

subAllTTT :: [(Int, Type)] -> Type -> Type
subAllTTT [] t = t
subAllTTT (s:ss) t = subAllTTT ss (uncurry subTTT s t)