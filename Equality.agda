module Equality where

open import Relation.Binary.PropositionalEquality
-- open import Data.Nat using (_>?_) renaming (ℕ to Nat)
-- open import Agda.Builtin.Nat (_>_)

-- A set that does not contain anything
data Empty : Set where

-- A set with only one element
data Unit : Set where
  unit  : Unit

data Bool : Set where
  true  : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data Bin : Set where
  be : Bin
  b0 : Bin -> Bin
  b1 : Bin -> Bin

Not : (P : Set) -> Set
Not P = P -> Empty

data Dec (P : Set) : Set where
  yes : P     -> Dec P
  nop : Not P -> Dec P

data Pair : Set where
  pair : Nat -> Nat -> Pair

data _≤_ : Nat -> Nat -> Set where
  z≤n : ∀ {n}                 → zero   ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → succ m ≤ succ n

data Even : Nat -> Set where
  even-zero : Even zero
  even-succ : ∀ (n : Nat) -> Even n -> Even (succ (succ n))

-- even-zero : Even zero
-- even-succ : ∀ (n : Nat) -> Even n -> Even (succ (succ n))
--
-- even-succ 0 : Even 0 -> Even 2
-- even-succ 1 : Even 1 -> Even 3
-- even-succ 2 : Even 2 -> Even 4
-- even-succ 3 : Even 3 -> Even 5
-- even-succ 4 : Even 4 -> Even 6
-- even-succ 5 : Even 5 -> Even 7


--
--
--
-- foo : Nat -> Na
--
-- even-zero : Even zero
--
-- even-succ   : ∀ (n : Nat) -> Even n -> Even (succ (succ n))
-- even-succ 2 : Even 2 -> Even (succ (succ 2))

_<_ : Nat → Nat → Bool
_     < zero    = false
zero  < succ _  = true
succ n < succ m = n < m

-- Add two natural numbers
add : ∀ (n : Nat) -> ∀ (m : Nat) -> Nat
add zero      m     = m
add (succ n)  m     = succ (add n m)

-- Give the opposite value of a Bool
not : ∀ (bool : Bool) -> Bool
not true  = false
not false = true

or : ∀ (first : Bool) -> ∀ (second : Bool) -> Bool
or true  n     = true
or false m     = m

and : Bool -> Bool -> Bool
and true  true   = true
and m     n      = false

-- is-bigger-than : Nat -> Nat -> Bool
-- is-bigger-than a b with a >? b
-- ... | yes _ = true
-- ... | no _  = false


-- Identity function for booleans. Receives a bool and return itself.
id : Bool -> Bool
id b = b

-- Proof that id was correctly implemented
id-ok : ∀ (b : Bool) -> id b ≡ b
id-ok true  = refl
id-ok false = refl

-- Proof that and was correctly implemented
-- dec: a proof that "and a b" is true or a proof that "and a b" is not true
and-theorem-0 : ∀ (a : Bool) -> ∀ (b : Bool) -> ∀ (e : a ≡ true) -> Dec (and a b ≡ true)
and-theorem-0 .true true  refl = yes refl
and-theorem-0 .true false refl = nop (λ ())

and-ok-0 : ∀ (a : Bool) -> ∀ (b : Bool) -> ∀ (e : a ≡ false) -> and a b ≡ false
and-ok-0 .false m refl = refl

and-ok-1 : ∀ (a : Bool) -> ∀ (b : Bool) -> ∀ (e : a ≡ true) -> and a b ≡ b
and-ok-1 .true true  refl = refl
and-ok-1 .true false refl = refl

or-theorem-0 : ∀ (a : Bool) -> or a (not a) ≡ true
or-theorem-0 true  = refl
or-theorem-0 false = refl

and-theorem-1 : ∀ (a : Bool) -> and a (not a) ≡ false
and-theorem-1 true  = refl
and-theorem-1 false = refl

commutation : ∀ (a : Bool) -> ∀ (b : Bool) -> and a b ≡ and b a
commutation true true = refl
commutation true false = refl
commutation false true = refl
commutation false false = refl

-- demorgan
demorgan-0 : ∀ (a : Bool) -> ∀ (b : Bool) -> not (and a b) ≡ or (not a) (not b)
demorgan-0 true  true  = refl
demorgan-0 true  false = refl
demorgan-0 false true  = refl
demorgan-0 false false = refl

demorgan-1 : ∀ (a : Bool) -> ∀ (b : Bool) -> not (or a b) ≡ and (not a) (not b)
demorgan-1 true  true  = refl
demorgan-1 true  false = refl
demorgan-1 false true  = refl
demorgan-1 false false = refl

not-not : ∀ (a : Bool) → a ≡ not (not a)
not-not true  = refl
not-not false = refl

cake : ∀ (a : Bool) -> ∀ (e : a ≡ true) -> Nat
cake a e = 42

my-program-0 : ∀ (a : Bool) -> ∀ (b : Bool) -> ∀ (e : b ≡ or a (not a)) -> Nat
my-program-0 a b e =
  let before   = e                                -- b ≡ or a (not a)
      template = λ x -> b ≡ x                     -- (onde vai substituir no before)
      eq-proof = or-theorem-0 a                   -- or a (not a) ≡ true (lado esquerdo = antes, direito = depois)
      after    = (subst template eq-proof before) -- b ≡ true
  in (cake b after)

my-program-1 : ∀ (a : Bool) -> ∀ (b : Bool) -> ∀ (e : b ≡ not (not a)) -> b ≡ a
my-program-1 a b e =
  let template = λ x -> b ≡ x
      eq-proof = sym (not-not a)
      result   = (subst template eq-proof e)
  in result

-- Subtraction of natural number
sub : Nat -> Nat ->  Nat
sub (succ a) (succ b) = (sub a b)
sub a        zero     = a
sub zero     (succ x) = zero -- second element beign bigger that the first will result a negative number

-- add-zero-n : ∀ (n : Nat) -> add 0 n ≡ n
-- add-n-zero : ∀ (n : Nat) -> add n 0 ≡ n
-- even-6 : Even 6
-- is-even : ∀ (n : Nat) -> Dec (Even n)
-- double-is-even : ∀ (n : Nat) -> Even (double n)
-- add-n-n-double : ∀ (n : Nat) -> add n n ≡ double n -- nao sei se eh mt dificil


-- sub-ok : ∀ (n : Nat) -> ∀ (m : Nat) -> (mn) -> add n (sub m n) ≡ m
-- sub-ok n m = ?

-- TESTS --

id-ok-test : id false ≡ false
id-ok-test = id-ok false

dec-test : Dec Bool
dec-test = yes true

dec-test-2 : Dec (true ≡ true)
dec-test-2 = yes refl

dec-test-3 : Dec (true ≡ false)
dec-test-3 = nop λ ()

and-theorem-test : Dec (and true false ≡ true)
and-theorem-test = (and-theorem-0 true false refl)


sub-test : Nat
sub-test = (sub 10 3)

sub-negative-test : Nat
sub-negative-test = (sub 4 5)

-- f : Nat -> Nat
-- f = add 2
--
-- example : Nat
-- example = f 6


-- my-program-0-false-test : Nat
-- my-program-0-false-test = (my-program-0 false)
--
-- my-program-0-true-test : Nat
-- my-program-0-true-test = (my-program-0 true)

--
-- temos:
--   before   : Array (2 + 2) Bool
--   eq-proof : 2 + 2 ≡ 4
-- queremos:
--   after    : Array 4 Bool
--
-- let template = (λ x -> Array x Bool)
--     after    = subst template eq-proof before
--
-- temos:
--   before   : b ≡ or a (not a)
--   eq-proof : or a (not a) ≡ true
-- queremos:
--   after    : b ≡ true
--
-- let template = (λ x -> b ≡ x)
--     after    = subst template eq-proof before
