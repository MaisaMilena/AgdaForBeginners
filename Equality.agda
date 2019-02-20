module Equality where

open import Relation.Binary.PropositionalEquality

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

-- and-ok-0 : ∀ (a : Bool) -> ∀ (b : Bool) -> ∀ (e : a ≡ false) -> and a b ≡ false

-- and-ok-1 : ∀ (a : Bool) -> ∀ (b : Bool) -> ∀ (e : a ≡ false) -> and a b ≡ b

-- Prove esses teoremas
-- or-theorem-0 : ∀ (a : Bool) -> or a (not a) ≡ true
-- and-theorem-0 : ∀ (a : Bool) -> and a (not a) ≡ false

-- demorgan
-- demorgan-0 : ∀ (a : Bool) -> ∀ (b : Bool) -> not (and a b) ≡ or (not a) (not b)
-- demorgan-1 : ∀ (a : Bool) -> ∀ (b : Bool) -> not (or a b) ≡ and (not a) (not b)

-- Essa funcao so pode ser chamada se o input for true
cool : ∀ (a : Bool) -> ∀ (e : a ≡ true) -> Nat
cool a e = 42


-- Voce consegue chama-la no caso abaixo?
-- my-program-0 : ∀ (a : Bool) -> Nat
-- my-program-0 a = cool (or a (not a)) {!   !}

-- E no caso abaixo? (me avise quando chegar aqui, precisa de algo que nao ensinei ainda)
-- my-program-1 : ∀ (a : Bool) -> Nat
-- my-program-1 a = cool (or (not (not a)) (not a)) {!   !}


-- sub : Nat -> Nat -> Nat
-- sub-ok : ∀ (n : Nat) -> ∀ (m : Nat) -> (m > n) -> add n (sub m n) ≡ m


-- TESTS --
-- And --
andTrueTest : Bool
andTrueTest = (and true true)

andFalseTest : Bool
andFalseTest = (and true false)

andFalseTest2 : Bool
andFalseTest2 = (and false false)
-- Id --
idTrueTest : Bool
idTrueTest = (id true)

idFalseTest : Bool
idFalseTest = (id false)

id-ok-test : id false ≡ false
id-ok-test = id-ok false

dec-test : Dec Bool
dec-test = yes true

dec-test-2 : Dec (true ≡ true)
dec-test-2 = yes refl

dec-test-3 : Dec (true ≡ false)
dec-test-3 = nop λ ()

foo : Not (true ≡ false)
foo ()

and-theorem-test : Dec (and true false ≡ true)
and-theorem-test = (and-theorem-0 true false refl)
