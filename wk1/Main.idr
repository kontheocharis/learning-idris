module Main


-- Declaration ==     foo : X

-- Definition ==      foo : X
--                    foo m = n

-- Data definition == data Bar = Bing | Bang

-- Equation/clause == foo m = n


-- Bool = { True, False }
data Bool' : Type where
  True' : Bool'
  False' : Bool'

not : Bool' -> Bool'
not True' = False'
not False' = True'


-- Unit = { TT }
data Unit' : Type where
  TT : Unit'
           
-- Empty = { }
data Empty' : Type where
  


-- What about infinite sets???


-- Natural numbers


-- "inductive definition" of natural numbers
-- ℕ is a Set
-- 0 ∈ ℕ
-- ∀ n ∈ ℕ . n +1 ∈ ℕ

data Nat' : Type where
  Z' : Nat' -- 0 ∈ ℕ
  S' : Nat' -> Nat' -- ∀ n ∈ ℕ . n + 1 ∈ ℕ
  
zero : Nat'
zero = Z'
  
one : Nat'
one = S' Z'
  
two : Nat'
two = S' (S' Z') --- function application is not associative!! we have to put parentheses!
      
three : Nat'
three = S' two

-- forall = function with a labeled argument

add' : Nat' -> Nat' -> Nat'
add' Z' y = y
add' (S' x) y = S' (add' x y)

mult' : Nat' -> Nat' -> Nat'
mult' Z' y = Z'
mult' (S' x) y = add' y (mult' x y)

square : Nat' -> Nat'
square x = mult' x x

-- theorem = the type of a definition
-- proof   = a value/program of that type
-- "propositions as types" interpretation

-- left neutral
leftNeutral : (x : Nat') -> add' Z' x = x
leftNeutral x = Refl -- reflexivity == holds trivially

-- right neutral
rightNeutral : (x : Nat') -> add' x Z' = x
rightNeutral Z' = Refl -- show P 0
rightNeutral (S' x) = -- show P (k + 1)
    let ih = rightNeutral x -- assume P k
    in cong S' ih
    
-- Refl -- the only constructor of equality

-- cong -- function defined in prelude

-- if you have this, then you can show all of the below,
-- WITHOUT pattern matching on Refl
replace' : (0 p : a -> Type) -> p x -> x = y -> p y
replace' p inp Refl = inp

-- a -> Type   ---  a type with a free variable (and the free variable is of type a)

-- Additional exercise

cong' : (0 f : a -> b) -> x = y -> f x = f y
cong' f p = replace' (\k => f x = f k) Refl p

sym' : x = y -> y = x
sym' p = replace' (\k => k = x) Refl p

trans' : x = y -> y = z -> x = z
trans' p q = replace' (\k => x = k) p q

-- cong f p = ?dsj



-- Exercises:
--
-- associativity : (x + y) + z = x + (y + z)
-- commutativity : x + y = y + x

-- next time: lists, vectors, primitives, equality type

-- next next time: general inductive ADTs, generic printf

-- Addrightsucc
aux : (x, y : _) -> add' x (S' y) = S' (add' x y)
aux Z' b = Refl
aux (S' x) b = cong S' (aux x b)

commutativity : (x, y : _) -> add' x y = add' y x
commutativity Z' Z' = Refl
commutativity Z' (S' x) = cong S' (commutativity Z' x)
commutativity (S' x) Z' = cong S' (commutativity x Z') 
commutativity (S' x) (S' y) = cong S' (trans (aux x y) (trans (cong S' (commutativity x y)) (sym (aux y x))) )

  -- cong S' (trans (aux x y) (trans (cong S' (commutativity x y)) (sym (aux y x))))