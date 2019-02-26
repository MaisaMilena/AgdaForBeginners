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

-- Add two natural numbers
add : ∀ (n : Nat) -> ∀ (m : Nat) -> Nat
add zero      m     = m
add (succ n)  m     = succ (add n m)

-- Receives a Nat and sum all numbers before it
sum : Nat -> Nat
sum n = {!   !}

-- data List (A : Set) : Set where
--   cons : (x : A) -> (xs : List A) -> List A
--   nil  : List A
--
-- data Maybe (A : Set) : Set where
--   some : A -> Maybe A
--   none : Maybe A
--
-- map : (A : Set) -> (B : Set) -> (xs : List A) -> (f : A -> B) -> List B
-- map A B xs f = {!   !}
--
-- filter : (A : Set) -> (cond : A -> Bool) -> (xs : List A) -> List A
-- filter A cond xs = {!   !}
--
-- index : (A : Set) -> (i : Nat) -> List A -> Maybe A
-- index A i xs = {!   !}
--
-- find : (A : Set) -> (cond : A -> Bool) -> List A -> Nat
-- find A cond xs = {!   !}
