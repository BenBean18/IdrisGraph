module AsList

import Data.List
import Data.Nat
import Debug.Trace
import Data.SortedMap
import Data.Vect
import Data.Rel
import Decidable.Equality

Polynomial : Nat -> Type
Polynomial n = Vect n Int

(n: Nat) => Num (Polynomial n) where
    fromInteger i = case n of
        (S k) => 
            let zeroes: Vect k Int = (replicate k 0)
                newList : Vect (S k) Int = (cast i) :: zeroes in newList
    
    (*) a b = replicate n 0

    (+) a b = case n of 
        Z => []
        (S k) => addPoly a b where
            addPoly : {k: Nat} -> Polynomial (S k) -> Polynomial (S k) -> Polynomial (S k)
            addPoly (a1::a) (b1::b) = (a1 + b1) :: (a + b)

(*) : Int -> Polynomial n -> Polynomial n
(*) s = map (* s)

indices : {n : Nat} -> Vect n a -> Vect n (Fin n)
indices {n = Z} [] = []
indices {n = S k} (v :: vs)= FZ :: map FS (indices {n = k} vs)

enumerate: {n: Nat} -> Vect n a -> Vect n (Pair (Fin n) a)
enumerate v = zip (indices v) v

mapIndexed: {n: Nat} -> (Pair (Fin n) a -> b) -> Vect n a -> Vect n b 
mapIndexed f v = map f (zip (indices v) v)

testing : Polynomial 4
testing = fromInteger 3

pad : {n: Nat} -> Polynomial n -> Polynomial (S n)
-- pad v = 
--     let prf1 : (1 + n = S n) = plusOneSucc n
--         prf2 : (n + 1 = 1 + n) = rewrite (plusCommutative n 1) in Refl
--         prf : (n + 1 = S n) = rewrite prf1 in rewrite prf2 in Refl
--         fn : (Vect (n + 1) Int -> Vect (S n) Int) = rewrite prf in id
--         in fn (v ++ [0])
pad v = v `snoc` 0

padRight : {n : Nat} -> {i : Nat} -> Vect i Int -> Vect n Int
padRight v = case exactLength n v of
    Just v' => v'
    Nothing => padRight (v ++ [0])

upOne : {n: Nat} -> Polynomial n -> Polynomial (S n)
upOne v = 0 :: v

{-
     power: 0 1 2 3 4 
1 + 2x + 3x^2 = 1 2 3 0...
x = 0 1 0...

result should be 0 1 2 3 0...

0 * (1 2 3 0) =    0 0 0 0 z
. 1 * (1 2 3 0) =  . 1 2 3 0 z

 -}

%default total

mul : {fl : Nat} -> {sl : Nat} -> Polynomial fl -> Polynomial sl -> Vect (fl + sl) Int
mul (x :: []) second = pad (x * second)
mul (x :: xs) second =
    let currentProduct : Polynomial (S sl) = pad (x * second)
        result = upOne (mul xs second) in padRight currentProduct + padRight result
mul _ _ = []