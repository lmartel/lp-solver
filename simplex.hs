{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Simplex where
import Data.List
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as Vec

newtype Poly a = P (Vector a)

instance (Show a, Num a, Eq a) => Show (Poly a) where
  show (P cs) = intercalate " + " . filter (/= "") . map showTerm $ zip (Vec.toList cs) [0..]
    where showTerm :: (Show a, Num a, Eq a) => (a, Int) -> String
          showTerm (c, i)
            -- | c == 0    = "" -- TODO use this line to hide terms with coefficient 0
            | otherwise = show c ++ "(x_" ++ show i ++ ")"

instance Num a => Num (Poly a) where
    (+) = polyPlus
     where polyPlus :: Num a => Poly a -> Poly a -> Poly a
           polyPlus (P p1) (P p2) = P $ addCoefs p1 p2
           addCoefs :: Num a => Vector a -> Vector a -> Vector a
           addCoefs xs ys
             | null xs = ys
             | null ys = xs
             | otherwise = Vec.cons (Vec.head xs + Vec.head ys) $ addCoefs (Vec.tail xs) (Vec.tail ys)

    (*) = undefined -- not sure if needed
    negate (P cs) = P (Vec.map negate cs)
    fromInteger i = P . Vec.singleton $ fromInteger i
    -- Undefined operations on polynomials
    abs    = undefined
    signum = undefined

instance Foldable Poly where
  foldr fn b (P v)
    | null v    = b
    | otherwise = foldr fn (fn (Vec.head v) b) (Vec.tail v)


newtype Min a = Min (Poly a) deriving Show
newtype Max a = Max (Poly a) deriving Show
data Objective a = OMin (Min a) | OMax (Max a)

instance (Show a, Num a, Eq a) => Show (Objective a) where
  show (OMin m) = show m
  show (OMax m) = show m

data Leql a = Leql (Poly a) a
data Eql a = Eql (Poly a) a
data Geql a = Geql (Poly a) a
data Constraint a = LEC (Leql a) | EC (Eql a) | GEC (Geql a)

data NonNeg = NonNeg
data URS = URS
data Bound = Unbound URS | NNBound NonNeg

showBound :: Int -> Bound -> String
showBound i (Unbound _) = "x_" ++ show i ++ " urs"
showBound i (NNBound _) = "x_" ++ show i ++ " ≥ 0"

class PrettyPrint a where
  pp :: a -> String

instance PrettyPrint (Vector URS) where
  pp urs = intercalate ", " . map (\(i, ur) -> showBound i $ Unbound ur) . zip [0..] $ Vec.toList urs

instance PrettyPrint (Vector NonNeg) where
  pp nns = intercalate ", " . map (\(i, nn) -> showBound i $ NNBound nn) . zip [0..] $ Vec.toList nns

instance PrettyPrint (Vector Bound) where
  pp bs = intercalate ", " . map (uncurry showBound) $ zip [0..] (Vec.toList bs)

instance (Show a, Num a, Eq a) => Show (Leql a) where
  show (Leql p v) = show p ++ " ≤ " ++ show v

instance (Show a, Num a, Eq a) => Show (Eql a) where
  show (Eql p v) = show p ++ " = " ++ show v

instance (Show a, Num a, Eq a) => Show (Geql a) where
  show (Geql p v) = show p ++ " ≥ " ++ show v

instance (Show a, Num a, Eq a) => Show (Constraint a) where
  show (LEC c) = show c
  show (EC c) = show c
  show (GEC c) = show c

instance Num a => Num (Leql a) where
  (+) (Leql p v) (Leql p2 v2) = Leql (p + p2) (v + v2)

instance Num a => Num (Eql a) where
  (+) (Eql p v) (Eql p2 v2) = Eql (p + p2) (v + v2)

instance Num a => Num (Geql a) where
  (+) (Geql p v) (Geql p2 v2) = Geql (p + p2) (v + v2)

instance Num c => Num (Constraint c) where
  negate (LEC (Leql p v)) = GEC $ Geql (negate p) (negate v)
  negate (EC (Eql p v)) = EC $ Eql (negate p) (negate v)
  negate (GEC (Geql p v)) = LEC $ Leql (negate p) (negate v)
  -- Sometimes undefined on constraints
  (+) (LEC c1) (LEC c2) = LEC (c1 + c2)
  (+) (EC c1)  (EC c2)  = EC  (c1 + c2)
  (+) (GEC c1) (GEC c2) = GEC (c1 + c2)
  (+) _ _ = undefined
  -- Always undefined on constraints
  (*) = undefined
  fromInteger = undefined
  abs = undefined
  signum = undefined


data LinearProgram obj con bound a = LP (obj a) (Vector (con a)) (Vector bound)
objective (LP o _ _) = o
constraints (LP _ cs _) = cs
bounds (LP _ _ bs) = bs

instance (Show (o a), Show (c a), PrettyPrint (Vector b), Show a, Num a, Eq a) => Show (LinearProgram o c b a) where
  show (LP obj cs bs) = intercalate "\n" $
                     ("LP: " ++ show obj ++ ", s.t.")
                     : map show (Vec.toList cs)
                     ++ ["and " ++ pp bs]



-- type GenLP a = LinearProgram Objective Constraint Bound a
-- type StdLP a = LinearProgram Max Eql Geql a
-- type VarMap a = Map.Map Int a
-- data LPSolution a = LPSolution (StdLP a) (VarMap a)

-- Custom typeclasses
class ContainsPoly p where
  pMap :: (Poly a -> Poly a) -> p a -> p a
  poly :: p a -> Poly a

instance ContainsPoly Min where
  pMap fn (Min p) = Min (fn p)
  poly (Min p) = p

instance ContainsPoly Max where
  pMap fn (Max p) = Max (fn p)
  poly (Max p) = p

instance ContainsPoly Objective where
  pMap fn (OMin m) = OMin (pMap fn m)
  pMap fn (OMax m) = OMax (pMap fn m)

  poly (OMin m) = poly m
  poly (OMax m) = poly m

instance ContainsPoly Leql where
  pMap fn (Leql p v) = Leql (fn p) v
  poly (Leql p _) = p

instance ContainsPoly Eql where
  pMap fn (Eql p v) = Eql (fn p) v
  poly (Eql p _) = p

instance ContainsPoly Geql where
  pMap fn (Geql p v) = Geql (fn p) v
  poly (Geql p _) = p

instance ContainsPoly Constraint where
  pMap fn (LEC c) = LEC $ pMap fn c
  pMap fn (EC c)  = EC  $ pMap fn c
  pMap fn (GEC c) = GEC $ pMap fn c

  poly (LEC c) = poly c
  poly (EC c) = poly c
  poly (GEC c) = poly c


---- Helper functions

coeff :: Num a => Int -> Poly a -> a
coeff nth (P xs) = case xs Vec.!? nth of
  Just x -> x
  Nothing -> 0

pConcat :: Poly a -> Vector a -> Poly a
pConcat (P xs) ys = P $ xs Vec.++ ys

pAppend :: Poly a -> a -> Poly a
pAppend (P xs) x = P $ Vec.snoc xs x

apC :: (c a -> c a) -> Int -> LinearProgram o c b a -> LinearProgram o c b a
apC f i lp@(LP o cs bs) = case cs Vec.!? i of
  Nothing -> lp
  Just c -> LP o (cs Vec.// [(i, f c)]) bs

mapC :: (c a -> c' a) -> LinearProgram o c b a -> LinearProgram o c' b a
mapC f (LP o cs bs) = LP o (Vec.map f cs) bs

consC :: c a -> LinearProgram o c b a -> LinearProgram o c b a
consC c (LP o cs bs) = LP o (Vec.cons c cs) bs

consB :: b -> LinearProgram o c b a -> LinearProgram o c b a
consB b (LP o cs bs) = LP o cs (Vec.cons b bs)

appendB :: LinearProgram o c b a -> b -> LinearProgram o c b a
appendB (LP o cs bs) b = LP o cs (Vec.snoc bs b)

numVars :: ContainsPoly c => LinearProgram o c b a -> Int
numVars (LP _ cs _) = foldl max 0 . Vec.map (\(P xs) -> length xs) $ Vec.map poly cs

padWithDefaults :: (ContainsPoly o, ContainsPoly c) => a -> b -> LinearProgram o c b a -> LinearProgram o c b a
padWithDefaults da db l = flip padBounds db . flip padConstraints da $ padObjective l da
  where padObjective :: (ContainsPoly o, ContainsPoly c) => LinearProgram o c b a -> a -> LinearProgram o c b a
        padObjective lp@(LP o cs bs) a = LP (padTo (numVars lp) a o) cs bs
        padConstraints :: ContainsPoly c => LinearProgram o c b a -> a -> LinearProgram o c b a
        padConstraints lp a = mapC (padTo (numVars lp) a) lp
        padTo :: (ContainsPoly c) => Int -> a -> c a -> c a
        padTo n x c
          | n <= length (poly c) = c
          | otherwise            = padTo n x $ pMap (`pAppend` x) c
        padBounds :: ContainsPoly c => LinearProgram o c b a -> b -> LinearProgram o c b a
        padBounds lp b = applyToBs lp $ flip (!!) (numVars lp - length (bounds lp)) . iterate (`Vec.snoc` b)
        applyToBs (LP o cs bs) fun = LP o cs (fun bs)

-- Add a variable with bound `b` to each constraint
appendVar :: (Num a, ContainsPoly o, ContainsPoly c) => LinearProgram o c b a -> b -> LinearProgram o c b a
appendVar (LP o cs bs) b = LP (pad o) (Vec.map pad cs) (Vec.snoc bs b)
  where pad :: (Num a, ContainsPoly b) => b a -> b a
        pad = pMap (`pAppend` 0)


---- LP manipulation functions

standardForm :: Num a => LinearProgram Objective Constraint Bound a -> LinearProgram Max Eql NonNeg a
standardForm = constraintsToEqualities . boundUnrestrictedVars . shadowUnrestrictedVars . convertToMaximization . padWithDefaults 0 (Unbound URS)

convertToMaximization :: Num a => LinearProgram Objective Constraint Bound a -> LinearProgram Max Constraint Bound a
convertToMaximization (LP (OMin m) cs bs) = LP (Max . negate $ poly m) cs bs
convertToMaximization (LP (OMax m) cs bs) = LP m cs bs

constraintsToEqualities :: (Num a, ContainsPoly o) => LinearProgram o Constraint NonNeg a -> LinearProgram o Eql NonNeg a
constraintsToEqualities lp = case findInequality lp of
                              Nothing -> mapC unwrapEquality lp
                              Just i -> constraintsToEqualities $ convertToEquality lp i
  where findInequality :: LinearProgram o Constraint b a -> Maybe Int
        findInequality (LP _ cs _) = Vec.findIndex (\c -> case c of (EC _) -> False; _ -> True) cs
        unwrapEquality :: Constraint a -> Eql a
        unwrapEquality (EC eql) = eql
        unwrapEquality _ = error "Constraint does not contain an equality"
        convertToEquality :: (Num a, ContainsPoly o) => LinearProgram o Constraint NonNeg a -> Int -> LinearProgram o Constraint NonNeg a
        convertToEquality l i = apC slacken i $ appendVar l NonNeg
        slacken :: Num a => Constraint a -> Constraint a
        slacken (LEC (Leql p v)) = setSlack 1 p v
        slacken (EC (Eql p v)) = setSlack 0 p v
        slacken (GEC (Geql p v)) = setSlack (-1) p v
        setSlack :: Num a => a -> Poly a -> a -> Constraint a
        setSlack s p@(P vec) val = EC $ Eql ( case length vec of
                                               0 -> p
                                               _ -> P $ Vec.snoc (Vec.init vec) s
                                            ) val

shadowUnrestrictedVars :: (Num a, ContainsPoly o, ContainsPoly c) => LinearProgram o c Bound a -> LinearProgram o c Bound a
shadowUnrestrictedVars lp = foldl (flip shadowVar) lp $ findURS (bounds lp)
  where findURS :: Vector Bound -> [Int] -- Return all indices of (Unbound _) variables
        findURS bs = map fst . filter (\(_,b) -> isUnbound b) . zip [0..] $ Vec.toList bs
        isUnbound (Unbound _) = True
        isUnbound _ = False

-- Replace ax_i with (ax_i - ax_i')
shadowVar :: (Num a, ContainsPoly o, ContainsPoly c) => Int -> LinearProgram o c Bound a -> LinearProgram o c Bound a
shadowVar i (LP obj cs bs) = LP (pMap (shadow i) obj) (Vec.map (pMap $ shadow i) cs) bs
  where shadow :: Num a => Int -> Poly a -> Poly a
        shadow n p = pAppend p . negate $ coeff n p



-- Replace x_i URS with x_i >= 0, x_i' >= 0
boundUnrestrictedVars :: (Num a, ContainsPoly o, ContainsPoly c) => LinearProgram o c Bound a -> LinearProgram o c NonNeg a
boundUnrestrictedVars (LP obj cs bvec)
  | null bvec = LP obj cs Vec.empty
  | otherwise = let b = Vec.head bvec; bs = Vec.tail bvec in
                 case b of
                  (NNBound _) -> consB NonNeg $ boundUnrestrictedVars (LP obj cs bs)
                  (Unbound _) -> consB NonNeg $ boundUnrestrictedVars (LP obj cs . Vec.snoc bs $ NNBound NonNeg)




main :: IO ()
main = do
  let lp = LP (lpMin [-2, 3]) (Vec.fromList [
                                  leq [1, -3, 2] 3,
                                  geq [-1, 2] 2
                              ]) (Vec.fromList [urs, ge0, ge0])
  print lp
  print $ standardForm lp
  where mkP :: [Int] -> Poly Int
        mkP is = P $ Vec.fromList is
        lpMin :: [Int] -> Objective Int
        lpMin = OMin . Min . mkP
        leq :: [Int] -> Int -> Constraint Int
        leq cs v  = LEC $ Leql (mkP cs) v
        geq :: [Int] -> Int -> Constraint Int
        geq cs v = GEC $ Geql (mkP cs) v
        urs = Unbound URS
        ge0 = NNBound NonNeg
