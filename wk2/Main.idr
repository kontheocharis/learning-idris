module Main

%default total

-- some more data types




-- Lists of some element type
--
-- Lists of natural numbers
--
-- Lists of strings
-- Lists of lists of natural numbers..

data Unit' : Type where
  TT : Unit'

-- data List : Type -> Type where
--   Nil : List a
--   (::) : a -> List a -> List a

-- []        --- Nil
-- x :: xs   --- Cons x xs

-- Even more special syntax
---
--- [1, 2, 3, 5] === 1 :: 2 :: 3 :: 5 :: []

singleton : a -> List a
singleton x = [x]

repeat : Nat -> a -> List a
repeat 0 x = []
repeat (S k) x = x :: repeat k x

length' : List a -> Nat 
length' [] = 0
length' (x :: xs) = S (length' xs)

0 lengthRepeat : length' (repeat n x) = n
lengthRepeat {n = 0} = Refl
lengthRepeat {n = S k} = cong S lengthRepeat

-- 0 repeatLength : repeat (length' xs) x = xs
-- repeatLength {xs = []} = Refl
-- repeatLength {xs = y :: ys} = ?dsjjK

data Option : Type -> Type where
  None : Option a
  Some : a -> Option a


-- big problem
index : Nat -> List a -> Option a
index n [] = None
index 0 (x :: xs) = Some x
index (S k) (x :: xs) = index k xs

Holds : Bool -> Type
Holds x = (x = True)

Holds' : Bool -> Type
Holds' False = Void -- the type corresponding to false
Holds' True = Unit -- the type corresponding to true


data Holds'' : Bool -> Type where
  Yes : Holds'' True
  
data Equals : a -> a -> Type where
  Refl' : Equals x x
  
-- two kinds of equalities
-- 
-- 1. "definitional equality" --- equality the compiler knows about
-- 2. "propositional equality" --- the equality type
--         -> internalise definitional equality
--         -> p : x = y

notLtZero : {n : Nat} -> Holds (n < 0) -> Void 
notLtZero {n = 0} Refl impossible
notLtZero {n = S k} Refl impossible

-- absurd : Void -> a
-- absurd x impossible

-- still annoying
index' : (n : Nat) -> (l : List a) -> Holds (n < length l) -> a
index' n [] p = absurd (notLtZero p)
index' 0 (x :: xs) p = x
index' (S k) (x :: xs) p = index' k xs p

-- index 0 [1, 2, 3] != Some 1

-- Homework:
--
-- 1. Given a natural number n, define the type `Fin` of natural numbers less
--    than n, using `data`. Fin : Nat -> Type
--
-- 2. Define the type of *vectors* -- lists that are indexed by their length
--    Vect : Nat -> Type -> Type
--
-- 3. Define a much nicer looking safe `index` function that uses Fin and Vect
--    instead of List and Nat.


