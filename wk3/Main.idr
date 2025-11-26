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

lt : Nat -> Nat -> Bool
0 `lt` 0 = False
0 `lt` (S k) = True
(S k) `lt` (S k') = k `lt` k'
(S k) `lt` 0 = False

-- still annoying
index' : (n : Nat) -> (l : List a) -> Holds (n < length l) -> a
index' n [] p = absurd (notLtZero p) -- <- proof of false
index' 0 (x :: xs) p = x
index' (S k) (x :: xs) p = index' k xs p -- : Holds (k < length xs)
                -- : Holds (S k < length (x :: xs))  
                -- : Holds (S k < S (length xs))  
                -- : Holds (k < length xs)  

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



-- data List : Type -> Type where
--   Nil : List a
--   (::) : a -> List a -> List a


-- (a, b) -- "the set of tuples of elements picked from a and from b"

tt : ()  -- the set containing a single element
tt = ()

ttunit : {a : ()} -> a = ()
ttunit {a = ()} = Refl

first : (a, b) -> a
first (x, y) = x

second : (a, b) -> b
second (x, y) = y

pair : a -> b -> (a, b)
pair x y = (x, y)

-- β laws for pairs

firstPair : first (pair x y) = x
firstPair = Refl

secondPair : second (pair x y) = y
secondPair = Refl

-- η law for pairs
pairFirstSecond : pair (first p) (second p) = p
pairFirstSecond {p = (x, y)} = Refl


-- best practice for types: only simple (not nested) matches.
Vector : Nat -> Type -> Type
Vector 0 a = ()
Vector (S k) a = (a, Vector k a)

Vector3Nat : Type
Vector3Nat = Vector 3 Nat

prf : Vector3Nat = (Nat, Nat, Nat, ())
prf = Refl

test : Vector3Nat
test = (1, 2, 3, ())

-- simple pairs
-- (a, b)          --- cartesian product of a and b

-- dependent pairs
-- (x : a ** b x)  --- "there exists an x : a such that b x holds"  (interpreting b as a proposition)

-- (x : Nat ** Holds (1 < x)) -- there exists a natural number x such that 1 < x
-- 
-- ∑_(x:Nat) (Holds (1 < x))
-- Holds (1 < 0) + Holds (1 < 1) + Holds (1 < 2) + Holds (1 < 3) + ..
-- -- indexed disjoint union
-- 
-- (x : Nat ** (x = 3) `OR` (x = 4)) = { (3, Refl), (4, Refl) }

-- (a, b)          -- cartesian product (multiplication for types: x = |a| , y = |b|, x * y = |(a, b)|)
-- Either (+) (Result) -- disjoint union (addition for types: x = |a| , y = |b|, x + y = |a OR b|)

-- data Either : Type -> Type -> Type where
--   Left : a -> Either a b
--   Right : b -> Either a b
  
DepPair : (a : Type) -> (b : a -> Type) -> Type
DepPair a b = (x : a ** b x)

List' : Type -> Type
List' a = (n : Nat ** Vector n a)

-- (n : Nat ** Vector n a)
-- 
-- (0 ** ())
-- (1 ** (x, ()))         (forall x : a)
-- (2 ** (x, y, ()))      (forall x, y : a)
-- ...

threeOnes : List' Nat
threeOnes = (3 ** (1, 1, 1, ()))

nil : List' a
nil = (0 ** ())

cons : a -> List' a -> List' a
cons x (n ** xs) = (S n ** (x, xs))

singleton' : a -> List' a
singleton' x = (1 ** (x, ()))


repeat'' : a -> (n : Nat) -> Vector n a 
repeat'' x 0 = ()
repeat'' x (S k) = (x, repeat'' x k)

repeat' : a -> Nat -> List' a
repeat' x n = (n ** repeat'' x n)

Any : Type
Any = (b : Type ** b) -- maximum information loss
                      -- emulate dynamic typing in Idris

repeat''' : (a : Type) -> a -> Nat -> Any
repeat''' a x n = (List' a ** repeat' x n)


foo : List Nat
foo = [1, 2, 3]

-- foo' : List' Nat
-- foo' = (_ ** (1, 2, 3, ()))



-- I'm asking the compiler to solve
-- Vector ? Nat = (Nat, Nat, Nat, ())

--
-- if i have some
--
--    x : a
--
-- and a function that looks like
--
--    f : (y : a) -> b y
--
-- then i can create an element of
--
--   (y : a ** b y)
--
-- by giving
--
--   (x ** f x)

nil' : Vector 0 a
nil' = ()

cons' : a -> Vector n a -> Vector (S n) a
cons' x xs = (x, xs)

-- data List : Type -> Type where
--   Nil : List a
--   Cons : a -> List a -> List a


-- Vector : Nat -> Type -> Type
-- Vector 0 a = ()
-- Vector (S k) a = (a, Vector k a)

data Vector' : Nat -> Type -> Type where
  Nil' : Vector' 0 a
  Cons' : a -> Vector' n a -> Vector' (S n) a
  
 
good : Vector' ? Nat
good = Cons' 3 (Cons' 4 Nil')

bad : Vector 2 Nat
bad = cons' {n = 1} 3 (cons' {n = 0} 4 (nil' {a = Nat}))

-- Homework same as before