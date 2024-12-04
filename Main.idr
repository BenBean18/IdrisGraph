module Main

import Data.List
import Data.Nat
import Debug.Trace
import Data.SortedMap
import Data.Vect

record Term where
    constructor Monomial
    c : Integer
    p : Nat

Show Term where
    show (Monomial c p) = show c ++ "x^" ++ show p

Polynomial : Type
Polynomial = List Term

total factorial : Nat -> Nat
factorial (S k) = (S k) * factorial k
factorial Z = 1

choose : Nat -> Nat -> Nat
choose n k = (factorial n) `div` ((factorial k) * (factorial (n `minus` k)))

coeff : Nat -> Nat -> Integer -> Term
coeff n p sign = Monomial (sign * natToInteger ( (n `minus` ((n `minus` p) `div` 2)) `choose` (2* (p `div` 2) + (n `mod` 2))) ) p

-- sign starts off - for odd power, + for even power
P' : Nat -> Nat -> Integer -> Polynomial
P' n (S (S prevPower)) sign =
    let p = S (S prevPower) in coeff n p sign :: P' n prevPower (0 - sign)
P' n p sign = [coeff n p sign]

P : Nat -> Polynomial
P n = P' n n (if n `mod` 2 == 0 then 1 else (-1))

polyToStr : Polynomial -> String
polyToStr (term :: terms) = " + " ++ show term ++ polyToStr terms
polyToStr [] = ""

Num Term where
    fromInteger i = Monomial i 0

    (*) (Monomial c1 p1) (Monomial c2 p2) = Monomial (c1 * c2) (p1 * p2)

    (+) (Monomial c1 p1) (Monomial c2 p2) = if p1 == p2 then Monomial (c1 + c2) p1 else Monomial 0 0 -- should be able to pattern match (Monomial c1 p) (Monomial c2 p) but get weird error

-- NEEDS A SORTED LIST BY POWER
combineLikeTerms : List Term -> List Term
combineLikeTerms ((Monomial c1 p1) :: (Monomial c2 p2) :: xs) =
    if p1 == p2 then [Monomial (c1 + c2) p1] ++ combineLikeTerms xs else (Monomial c1 p1) :: (Monomial c2 p2) :: combineLikeTerms xs
combineLikeTerms (m :: []) = [m]
combineLikeTerms [] = []

Eq Term where
    (==) (Monomial c1 p1) (Monomial c2 p2) = c1 == c2 && p1 == p2

Ord Term where
    (<) (Monomial _ p1) (Monomial _ p2) = p1 < p2

normalize : Polynomial -> Polynomial
normalize a = (sort (filter (\(Monomial c _) => c /= 0) a))

Num (List Term) where
    fromInteger i = [Monomial i 0]

    (*) a b = concatMap (\(Monomial c1 p1) => map (\(Monomial c2 p2) => Monomial (c1 * c2) (p1 + p2)) b) a -- WE JUST IMPLEMENTED POLYNOMIAL MULTIPLICATION

    -- OH MY GOSH
    -- COMBINING LIKE TERMS IS SORTING AND IF ADJACENT POWERS ARE EQUAL THEN ADDING COEFFICIENTS
    (+) a b = combineLikeTerms (sort (a ++ b))

-- begin thomas code
mat: Nat -> Type -> Type
mat n a = Vect n (Vect n a)

map2D: (a -> b) -> Vect n (Vect m a) -> Vect n (Vect m b)
map2D f v = map (\u => map f u) v

indices : {n : Nat} -> Vect n a -> Vect n (Fin n)
indices {n = Z} [] = []
indices {n = S k} (v :: vs)= FZ :: map FS (indices {n = k} vs)

enumerate: {n: Nat} -> Vect n a -> Vect n (Pair (Fin n) a)
enumerate v = zip (indices v) v

mapIndexed: {n: Nat} -> (Pair (Fin n) a -> b) -> Vect n a -> Vect n b 
mapIndexed f v = map f (zip (indices v) v)

even : Nat -> Integer
even Z = 1
even (S k) = odd k where
  odd : Nat -> Integer
  odd Z = -1
  odd (S k) = even k

det: Num a => {n: Nat} -> mat (S n) a -> a
det { n = Z } ((x :: []) :: []) = x
det { n = S k } rows =
    let a : Vect (S n) (Vect n (Vect n a)) = mapIndexed (\(i,e)=> (map (\v=>deleteAt i v) (deleteAt 0 rows))) rows
        b : ?t = zip (mapIndexed (\(i,e) => e*(fromInteger (even (finToNat i)))) (index 0 rows)) a
    in sum (map (\(e,m)=>e*(det m)) b)
    where 
        n = S k

gen: Num a => (n: Nat) -> mat n a
gen Z = []
gen (S k) = g k (gen k)
    where
        g: (k: Nat) -> mat k a -> mat (S k) a
        g 0 [] = (0 :: []) :: []
        g (S k) rows =  
            let v: Vect (S k) a = 1 :: (replicate k 0)
                l: Vect (S k) (Vect (S (S k)) a) = (map (\(x,xs)=> x :: xs) (zip v rows))
                s: Vect (S (S k)) (Vect (S (S k)) a) = (0 :: v) :: l
                in s
-- end thomas code

-- this doesn't work, because we end up adding different powers, which isn't supported, since that can't be captured in a single Term, since it's a *poly*nomial
-- Num (List Term)?
gen': (n: Nat) -> mat n Polynomial
gen' Z = []
gen' (S k) = g k (gen' k)
    where
        g: (k: Nat) -> mat k Polynomial -> mat (S k) Polynomial
        g 0 [] = (([Monomial (-1) 1]) :: []) :: []
        g (S k) rows =  
            let v: Vect (S k) Polynomial = 1 :: (replicate k 0)
                l: Vect (S k) (Vect (S (S k)) Polynomial) = (map (\(x,xs)=> x :: xs) (zip v rows))
                s: Vect (S (S k)) (Vect (S (S k)) Polynomial) = (([Monomial (-1) 1]) :: v) :: l
                in s

isDetEqConjecture : (n: Nat) -> Bool
isDetEqConjecture (S a) = normalize (det (gen' (S a))) == normalize (P (S a))
isDetEqConjecture Z = True

-- "proved" it
-- TODO fix, this is literally a proof by "trust me bro"
proveDetEqConjecture : (n: Nat) -> isDetEqConjecture n = True
proveDetEqConjecture n = believe_me $ Refl {x=True}

main : IO ()
main = do
    printLn (factorial 10)
    printLn (factorial 11)
    printLn (factorial 12)
    printLn (factorial 13)
    printLn (factorial 14)
    putStrLn (polyToStr (P 10))
    putStrLn (polyToStr (P 12))
    putStrLn (polyToStr (P 14))
    putStrLn (polyToStr (P 16))
    putStrLn (polyToStr (P 18))
    putStrLn (polyToStr (P 20))
    putStrLn (polyToStr (P 30))

-- 8 `choose` 0, 7 `choose` 2, 6 `choose` 4, 