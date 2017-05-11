
/**
* Author: 	Lorelon 
* Date:		11/05/2017
* 
**/


module Term where

import Data.List

type Term = String
type FunSymb = (Char, Int)
type Var = String
type Sub t = [(Var, Exp t)]
type ExpTuple t = (Exp t, Exp t)
type ETupleSet t = [ExpTuple t]
type Unification t = Maybe (Exp t, Sub t)
type Rule t = (Exp t, Exp t)

data Exp t = CNTX | Variable Var | Constant t | Function (Char) ([Exp t]) deriving Eq

instance (Show a) => Show (Exp a) where
 show (Variable v) = v
 show (Constant c) = show c
 show (Function f ls) = f : "(" ++ tail (foldl (\xs c -> xs++","++ show c) "" ls) ++ ")"

--apply substitution to an expression 
substitute :: Sub t -> Exp t -> Exp t
substitute sub expr = case sub of
 (x:y:s) -> let
  xs' = markConflicts (x:y:s)
  expr' = foldr (\sub ex -> substitute' sub ex) expr xs'
  in unMarkConf expr'
 (x:[]) -> substitute' x expr
 [] -> expr

--helper method that applies a substitution of exactly one variable
substitute' :: (Var, Exp t) -> Exp t -> Exp t
substitute' (var, val) expr  = case expr of
 Variable v -> if (v==var) then val else expr
 Function c ls -> Function c (map (substitute' (var, val)) ls)
 _ -> expr  
 
 --Removes the ' markers before the conflicting variables
unMarkConf :: Exp t -> Exp t 
unMarkConf expr = case expr of
 Variable v -> if ('\''==(head v)) then Variable (tail v) else expr
 Constant c -> expr
 Function f xs -> Function f (map unMarkConf xs)
 
--Sets markers for each variable that occures in the subs and the substitution
markConflicts :: Sub t -> Sub t
markConflicts xs = let
 exprs = map snd xs
 vars = map fst xs
 vals = rmDupl $ foldr (++) [] (map getVars exprs)
 conflicts = filter (\c -> elem c vars) vals
 subs c ls = map (\(a,b) -> (a, substitute' (c, Variable ("'"++c)) b)) ls
 in foldr (\c ys -> subs c ys) xs conflicts 
 
--get the list of variables the expression contains
getVars :: Exp t -> [Var]
getVars expr = case expr of
 Variable v -> [v]
 Constant c -> []
 Function _ xs -> foldr (\c ls -> ls ++ (getVars c)) [] xs

--concatenate two substitutions. removes duplicates afterwards. 
con :: (Eq t) => Sub t -> Sub t -> Sub t
con x [] = x
con [] y = y
con (x:[]) (y:[]) = if (fst x == fst y)
 then [(fst x, substitute' x (snd y))]
 else [x, (fst y, substitute' x (snd y) )]
con xs ys = let res = xs ++ (map (\(a,b) -> (a, substitute xs b)) ys)
 in rmDupl res

 --Unifies two expressions, if a unification exists.
unify :: (Eq t) => [Exp t] -> Unification t 
unify xs = let
 e0 = concat [diff x y | x <- xs, y <- xs, x/=y] --start with complete diff set
 sig0 = [] --and empty substitution
 result = iterateUni (e0, sig0) --run iteration untill e=[] or no rule can be applid
 in case result of
  ([],unif) -> Just (substitute unif (head xs),unif) --unifyable
  _ -> Nothing --not unifyable
 
--iterates unification over a set of differences and a substitution 
iterateUni :: (Eq t) => ([(Exp t, Exp t)], Sub t) -> ([(Exp t, Exp t)], Sub t)
iterateUni ([], sig) = ([], sig)
iterateUni (e, sig) = let
 (p,q) = head e --take first diff pair
 rules (a,b) = case a of
  Variable z -> varRule (a,b) (e, sig)
  Function f xs -> case b of
   Function g ys -> topRule (a,b) (e, sig)
   _ -> (e, sig)
  _ -> (e,sig)  --constant check abort
 in if (p==q)
  then iterateUni (tail e, sig)
  else rules (p,q)

varRule :: (Eq t) => (Exp t, Exp t) -> (ETupleSet t, Sub t) -> (ETupleSet t, Sub t)  
varRule (Variable z,t) (e, sig) = if (notElem z (getVars t)) --occurs check
 then iterateUni (map (\(x,y) -> (substitute [(z,t)] x, substitute [(z,t)] y)) e, con sig [(z,t)])
 else (e, sig) --occurs abort

topRule :: (Eq t) => ExpTuple t -> (ETupleSet t, Sub t) -> (ETupleSet t, Sub t)  
topRule (Function f xs, Function g ys) (e, sig) = if valid
 then ((tail e) ++ (concat (zipWith diff xs ys)), sig)
 else (e, sig) --top level abort
 where 
 	valid = f==g && length xs == length ys

diff :: (Eq t) => Exp t -> Exp t -> [(Exp t, Exp t)]
diff (Function f xs) (Function g ys) = if valid
 then concat $ zipWith diff xs ys
 else [((Function f xs),(Function g ys))]
 where
 	valid = f==g && length xs == length ys
diff x y = if (x==y) then [] else [(x,y)]

--true, iff x can be specialized to t through a substitution sigma
specialize :: (Eq t) => Exp t -> Exp t -> Maybe (Sub t)
specialize (Variable x) t = Just [(x, t)]
specialize (Constant a) b = if ((Constant a)==b) then Just [] else Nothing
specialize (Function f xs) (Function g ys) = if valid then concatMby res else Nothing
 where
 	res = zipWith specialize xs ys
 	valid = f==g && length xs == length ys
specialize _ _ = Nothing

--subsumption relation
infix 2 <<
(<<) :: (Eq t) => Exp t -> Exp t -> Bool
(<<) x y = case specialize x y of
	Just t -> True
	_ -> False

--strict subsumption relation
infix 2 <<!
(<<!) :: (Eq t) => Exp t -> Exp t -> Bool
(<<!) x y = (x << y) && (not (y << x))

--alpha equivalence on expressions
infix 2 ==~
(==~) :: (Eq t) => Exp t -> Exp t -> Bool
(==~) x y = (x << y) && (y << x)

--helper method to remove duplicates from a list
rmDupl :: (Eq a) => [a] -> [a]
rmDupl = foldl (\seen x -> if x `elem` seen then seen else seen ++ [x]) []

--concate a list of Maybe items. Returns Nothing, iff one or more elements are Nothing
concatMby :: [Maybe (Sub t)] -> Maybe (Sub t)
concatMby xs = foldl (\a b -> foo a b) (Just []) xs
 where foo a b = case (a,b) of
 	(Just w, Just v) -> Just (w++v)
 	(Nothing, _) -> Nothing
 	(_, Nothing) -> Nothing

disjunct :: Exp t -> Exp t -> Exp t
disjunct t1 t2 = foldr (\var ex -> substitute [(var, Variable (var++var))] ex) t2 (getVars t1)

disjRules :: Rule t -> Rule t -> Rule t
disjRules (t1, t2) (s1, s2) = let
  s1' = disjunct t2 (disjunct t1 s1)
  s2' = disjunct t2 (disjunct t1 s2)
  in (s1',s2')

nonVarPartTerm :: (Eq t) => Exp t -> [Exp t]
nonVarPartTerm t = let res = rmDupl $ nonVarPTerm' t []
  in res
--    (l:ls) -> Just res
--    [] -> Nothing

nonVarPTerm' :: Exp t -> [Exp t] -> [Exp t]
nonVarPTerm' (Variable x) ls = ls
nonVarPTerm' (Constant a) ls = ls ++ [(Constant a)]
nonVarPTerm' (Function f fs) ls = ls ++ [(Function f fs)] ++ (concat (map (\c -> nonVarPTerm' c ls) fs))

criticalP ::  (Eq t) => Rule t -> Rule t -> Maybe (Exp t, Exp t)
criticalP (t1,t2) r2 = let
  (s1, s2) = disjRules (t1,t2) r2
  --critList =  [unify [t2,x] | x <- nonVarPartTerm t1, unify [t2,x] /= Nothing]
  --varTTerm <- nonVarPartTerm t1
  unif = unify [s1, t1]
  in case unif of
    Just (_, sub) -> Just (substitute sub s1, s2)

position :: Exp t -> Int -> Maybe (Exp t)
position t 0 = Just t
position (Function f ls) n = if (n'-1 < lls) then position (ls!!n) (n-n') else Nothing
  where
    lls = length ls
    n' = n `mod` lls