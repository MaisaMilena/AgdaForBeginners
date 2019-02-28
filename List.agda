module List where

open import Relation.Binary.PropositionalEquality

-- A set that does not contain anything
data Empty : Set where

empty-elim : (P : Set) -> Empty -> P
empty-elim P ()

data Bool : Set where
  true  : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

Not : (P : Set) -> Set
Not P = P -> Empty

-- Different from Bool, shows an evidence of why the value is "yes" or "nop"
data Dec (P : Set) : Set where
  yes : P     -> Dec P
  nop : Not P -> Dec P

-- List é um conjunto que possui como elementos conjuntos do tipo A?
data List (A : Set) : Set where
  nil  : List A
  cons : (x : A) -> (xs : List A) -> List A

data Maybe (A : Set) : Set where
  none : Maybe A
  some : A -> Maybe A




-- Add two natural numbers
add : ∀ (n : Nat) -> ∀ (m : Nat) -> Nat
add zero      m     = m
add (succ n)  m     = succ (add n m)

-- Given a natural number, add 2 to its value
add-two : Nat -> Nat
add-two zero     = succ (succ zero)
add-two (succ n) = succ (succ (succ n))

-- Receives a Nat and sum all numbers before it. Is inclusive.
sum : Nat -> Nat
sum zero     = zero
sum (succ n) = (add (succ n) (sum n))

is-even : Nat -> Bool
is-even zero           = true
is-even (succ zero)    = false
is-even (succ(succ a)) = is-even a

-- Applies a given function to each element of the set
-- xs: a list of type A
-- f: a function that receives a Nat and returns a Nat
-- returns an element (nil or cons...) of type List B
map : (A : Set) -> (B : Set) -> (f : A -> B) -> (xs : List A)  -> List B
map A B f nil         = nil   -- empty list
map A B f (cons x xs) = cons (f x) (map A B f xs)
-- Note --
-- map f (cons 1 (cons 2 (cons 3 nil)))
-- cons (f 1) (map f (cons 2 (cons 3 nil)))
-- cons (f 1) (cons (f 2) (map f (cons 3 nil)))
-- cons (f 1) (cons (f 2) (cons (f 3) (map f nil)))
-- cons (f 1) (cons (f 2) (cons (f 3) nil))


-- Given a condition, filter the list to only return those cases that match the condition
-- cond: a function that determine a condition to be satisfied
-- xs: a list of type A
filter : (A : Set) -> (cond : A -> Bool) -> (xs : List A) -> List A
filter A cond nil         = nil -- empty list
filter A cond (cons x xs) with (cond x) -- looking into both possibities of cond result
filter A cond (cons x xs) | true  = cons x (filter A cond xs) -- add the element in the return list, keep looking the others
filter A cond (cons x xs) | false = (filter A cond xs) -- keep looking in the other elements

-- Count how many times a condition
count-cond : (A : Set) -> (cond : A -> Bool) -> (xs : List A) -> Nat
count-cond A cond nil         = zero -- empty list, no aplication of cond
count-cond A cond (cons x xs) with (cond x)  -- looking into both possibities of cond result
... | true  = succ (count-cond A cond xs) -- add 1 to the counter
... | false = (count-cond A cond xs) -- keep looking in the other elements

-- Lenght of a list in 1 line
length : (A : Set) -> (xs : List A) -> Nat
length A xs = (count-cond A (λ x -> true) xs)

-- not using
list-get-first : (A : Set) -> (xs : List A) -> List A
list-get-first A nil          = nil
list-get-first A (cons x nil) = (cons x nil) -- get the last number that is not zero
list-get-first A (cons x xs)  = (list-get-first A xs)

-- To create an empty list as a "variable", it must be represented as a new parameter.
-- Every recursive call adds a new element on "aux"
reverse-aux : (A : Set) -> (xs : List A) -> (aux : List A) -> List A
reverse-aux A nil aux         = aux
reverse-aux A (cons x xs) aux = (reverse-aux A xs (cons x aux))

-- Reverse a list
reverse : (A : Set) -> (xs : List A) -> List A
reverse A nil         = nil
reverse A (cons x xs) = (reverse-aux A (cons x xs) nil)


-- index : (A : Set) -> (i : Nat) -> List A -> Maybe A
-- index A i xs = {!   !}
--
-- find : (A : Set) -> (cond : A -> Bool) -> List A -> Nat
-- find A cond xs = {!   !}

-- muliplication


-- TEST --
list-nat : List Nat -- natural numbers list
list-nat = (cons 5 (cons 4 (cons 3 (cons 2 (cons 1 (cons 0 nil))))))

list-bool : List Bool
list-bool = (cons true (cons false (cons true nil)))

-- receives a list and a function to apply on each element
map-test : List Nat
map-test = map Nat Nat add-two list-nat

filter-test : List Nat
filter-test = (filter Nat is-even list-nat)

count-cond-test : Nat
count-cond-test = (count-cond Nat is-even list-nat)

length-test : Nat
length-test = (length Nat list-nat)

list-get-first-test : List Nat
list-get-first-test = (list-get-first Nat list-nat)

reverse-test : List Nat
reverse-test = (reverse Nat list-nat)
--
-- add-reverse-test : List Nat
-- add-reverse-test = (add-reverse Nat (cons 10 nil) list-nat)
