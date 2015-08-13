{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Simplex where
import Debug.Trace
import Data.List
import Data.Maybe
import Data.Either
import Control.Monad
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Matrix (Matrix)
import qualified Data.Matrix as Mat

newtype Poly a = P (Vector a)

coefficients :: Poly a -> Vector a
coefficients (P v) = v

instance (Show a, Num a, Eq a) => Show (Poly a) where
  show (P cs) = intercalate " + " . filter (/= "") . map showTerm $ zip (Vec.toList cs) [0..]
    where showTerm :: (Show a, Num a, Eq a) => (a, Int) -> String
          showTerm (c, i)
            -- | c == 0    = "" -- hide terms with coefficient 0
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

----- LP Solving Functions

data Assignment a = FullAssignment (Vector a) | PartialAssignment (Vector (Maybe a))
                  deriving Show

instance Functor Assignment where
  fmap fn (FullAssignment vec) = FullAssignment $ Vec.map fn vec
  fmap fn (PartialAssignment vec) = PartialAssignment $ Vec.map (fmap fn) vec

data MaybeSolution a =
  PartialSolution (Assignment a) (Vector (Eql a))
  | Finished (Assignment a)
  | Impossible String
  | Underspecified String

(<|) :: (Assignment a -> Vector (Eql a) -> MaybeSolution a) -> MaybeSolution a -> MaybeSolution a
fn <| (PartialSolution assn eqls) = fn assn eqls
_ <| Finished s = Finished s
_ <| Impossible s = Impossible s
_ <| Underspecified s = Underspecified s
infixl 1 <|

instance Show a => Show (MaybeSolution a) where
  show (PartialSolution assn eqls) = show assn ++ "\n" ++ show (toMatrix eqls)
  show (Finished assn) = show assn
  show (Impossible s) = "Impossible: " ++ s
  show (Underspecified s) = "Underspecified: " ++ s

finish :: Assignment a -> MaybeSolution a
finish a@(FullAssignment _) = Finished a
finish a@(PartialAssignment vs)
  | all isJust vs = Finished . FullAssignment $ Vec.map fromJust vs
  | otherwise     = Finished a

assignmentValues :: Assignment a -> Vector (Maybe a)
assignmentValues (FullAssignment vec) = Vec.map Just vec
assignmentValues (PartialAssignment vec) = vec

emptyAssignment :: Matrix a -> Assignment a
emptyAssignment = PartialAssignment . flip Vec.replicate Nothing . mNumVars

hasNonzeroCoeffs :: (Num a, Eq a) => Int -> Poly a -> Bool
hasNonzeroCoeffs n (P coeffs) = (== n) . Vec.length $ Vec.filter (/= 0) coeffs

nonzeroCoeffs :: (Num a, Eq a) => Poly a -> [Int]
nonzeroCoeffs (P coeffs) = map fst . filter ((/= 0) . snd) $ zip [1..] (Vec.toList coeffs)

isZeroP :: (Num a, Eq a) => Poly a -> Bool
isZeroP (P coeffs) = Vec.all (== 0) coeffs

applyP :: Num a => Assignment a -> Poly a -> a
applyP (PartialAssignment someValues) p = applyP (FullAssignment $ Vec.map (fromMaybe 0) someValues) p
applyP (FullAssignment values) (P coeffs) = sum . map computeTerm $ zip (Vec.toList $ Vec.zip coeffs values) [0..]
  where computeTerm ((c, v), e) = c * v
--where computeTerm ((c, v), e) = c * v^e TODO clarify single variable vs multivar polynomials

assign :: Num a => Assignment a -> Eql a -> Eql a
assign (FullAssignment values) = assignAt . zip [1..] $ Vec.toList values
assign (PartialAssignment values) = assignAt . mapMaybe (\(i, mv) -> case mv of
                                                 Just v -> Just (i, v)
                                                 Nothing -> Nothing
                                                 ) $ zip [1..] (Vec.toList values)
assignAt :: Num a => [(Int, a)] -> Eql a -> Eql a
assignAt [] p = p
assignAt ((n, v):rest) (Eql p@(P coeffs) k) = assignAt rest $ Eql (P $ coeffs Vec.// [(n-1, 0)]) (k + computedValue)
  where computedValue = applyP (FullAssignment oneAssignment) p
        oneAssignment = Vec.replicate (Vec.length coeffs) 0 Vec.// [(n-1, v)]

toSystemOfLinearEquations :: Num a => LinearProgram Max Eql NonNeg a -> Vector (Eql a)
toSystemOfLinearEquations lp = Vec.cons eqnFromObjective (constraints $ appendVar lp NonNeg)
  where eqnFromObjective = Eql (pAppend (negate . poly $ objective lp) 1) 0

toMatrix :: Vector (Eql a) -> Matrix a
toMatrix = Mat.fromLists . map eqlToList . Vec.toList
  where eqlToList (Eql (P vs) v) = Vec.toList vs ++ [v]

toEqualities :: Num a => Matrix a -> Vector (Eql a)
toEqualities = Vec.fromList . map listToEql . Mat.toLists
  where listToEql [] = Eql (P Vec.empty) 0
        listToEql vs = Eql (P . Vec.fromList $ init vs) (last vs)

simplifyEquality :: (Num a, Eq a) => Assignment a -> Eql a -> Either Bool (Eql a)
simplifyEquality assn e = resolveAssignment $ assign assn e
  where resolveAssignment e'@(Eql p' c')
          | isZeroP p'     = Left $ c' == 0
          | otherwise      = Right $ Eql p' c'

simplifyAllEqualities :: (Num a, Eq a) => Assignment a -> Vector (Eql a) -> Either Bool (Vector (Eql a))
simplifyAllEqualities assn eqls = reassembleSimplified . partitionEithers . map (simplifyEquality assn) $ Vec.toList eqls
  where reassembleSimplified :: ([Bool], [Eql a]) -> Either Bool (Vector (Eql a))
        reassembleSimplified ([], []) = Left True
        reassembleSimplified ([], eqs) = Right $ Vec.fromList eqs
        reassembleSimplified (solutions, eqs)
          | all (== True) solutions = reassembleSimplified ([], eqs)
          | otherwise               = Left False

mNumVars :: Matrix a -> Int
mNumVars m = Mat.ncols m - 1

-- A basic variable is a variable that shows up in exactly one equation.
-- Returns a list of basic variables, ONE-INDEXED.
-- Excludes the last column, since this is the "equalities" column and does not contain variable coefficients.
basicVars :: (Num a, Eq a) => Matrix a -> [Int]
basicVars m = filter (isBasic . flip Mat.getCol m)  $ take (mNumVars m) [1..]
  where isBasic :: (Num a, Eq a) => Vector a -> Bool
        isBasic col = length (Vec.filter (/= 0) col) == 1

nonBasicVars :: (Num a, Eq a) => Matrix a -> [Int]
nonBasicVars m = take (mNumVars m) [1..] \\ basicVars m

-- Assign all non-basic variables to 0, leaving basic variables unassigned.
nonBasicAssignment :: (Num a, Eq a) => Matrix a -> Assignment a
nonBasicAssignment m = PartialAssignment $ Vec.replicate (mNumVars m) Nothing Vec.// map (\nth -> (nth - 1, Just 0)) (nonBasicVars m)

basicSolution :: (Fractional a, Eq a) => Matrix a -> MaybeSolution a
basicSolution m = solveForBasicVars (basicVars m) <| solve (nonBasicAssignment m) (toEqualities m)

solve :: (Fractional a, Eq a) => Assignment a -> Vector (Eql a) -> MaybeSolution a
solve assn eqls = toSolution assn (simplifyAllEqualities assn eqls)

toSolution :: Assignment a -> Either Bool (Vector (Eql a)) -> MaybeSolution a
toSolution assn (Left True) = Finished assn
toSolution _ (Left False)   = Impossible "toSolution :: simplifyAll failed"
toSolution assn (Right vec) = PartialSolution assn vec

solveForBasicVars :: (Fractional a, Eq a) => [Int] -> Assignment a -> Vector (Eql a) -> MaybeSolution a
solveForBasicVars [] assn _ = finish assn
solveForBasicVars basics assn eqls = case popBasic basics eqls of
                                      Nothing -> Underspecified "No isolated basic variables left"
                                      Just (b, bs) -> solveForBasicVars bs <| solveBasic b assn eqls

popBasic :: (Num a, Eq a) => [Int] -> Vector (Eql a) -> Maybe (Int, [Int])
popBasic bs eqls = (\(b:_) -> Just (b, delete b bs)) =<< find (\cs -> length cs == 1) (map (\(Eql p _) -> nonzeroCoeffs p) (Vec.toList eqls))

solveBasic :: (Fractional a, Eq a) => Int -> Assignment a -> Vector (Eql a) -> MaybeSolution a
solveBasic nth assn eqls = packSolved nth assn eqls $ solveAt nth =<< Vec.find (\(Eql cs _) -> coefficients cs Vec.! (nth - 1) /= 0) eqls

packSolved :: (Num a, Eq a) => Int -> Assignment a -> Vector (Eql a) -> Maybe a -> MaybeSolution a
packSolved _ _ _ Nothing = Underspecified "solveBasic nth failed to find equality containing variable"
packSolved nth (PartialAssignment vals) eqls (Just newVal) = PartialSolution (PartialAssignment $ vals Vec.// [(nth - 1, Just newVal)]) (Vec.map (assignAt [(nth, newVal)]) eqls)

solveAt :: (Fractional a, Eq a) => Int -> Eql a -> Maybe a
solveAt nth (Eql (P cs) k)
  | k == 0       = Just 0
  | coeffAt == 0 = Just 0
  | otherwise    = Just $ k / coeffAt
      where coeffAt = cs Vec.! (nth - 1)


main :: IO ()
main = do
  let lp = LP (lpMin [-2, 3]) (Vec.fromList [
                                  leq [1, -3, 2] 3,
                                  geq [-1, 2] 2
                              ]) (Vec.fromList [urs, ge0, ge0])
  print lp
  let slp = standardForm lp
  print slp

  let slp2 = standardForm $ LP (lpMax [1, 1]) (Vec.fromList [
                                  leq [2, 1] 4,
                                  leq [1, 2] 3
                                  ]) (Vec.fromList [ge0, ge0])

  print slp2
  let les = toSystemOfLinearEquations slp2
  putStrLn . unlines . map show $ Vec.toList les
  let mat = toMatrix les
  print mat
  print $ basicSolution mat
  where mkP :: [Float] -> Poly Float
        mkP is = P $ Vec.fromList is
        lpMax :: [Float] -> Objective Float
        lpMax = OMax . Max . mkP
        lpMin :: [Float] -> Objective Float
        lpMin = OMin . Min . mkP
        leq :: [Float] -> Float -> Constraint Float
        leq cs v  = LEC $ Leql (mkP cs) v
        geq :: [Float] -> Float -> Constraint Float
        geq cs v = GEC $ Geql (mkP cs) v
        urs = Unbound URS
        ge0 = NNBound NonNeg
