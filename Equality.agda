module Equality where

open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)

-- A set that does not contain anything
data Empty : Set where

empty-elim : (P : Set) -> Empty -> P
empty-elim P ()

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

Not : (P : Set) -> Set
Not P = P -> Empty

-- Different from Bool, shows an evidence of why the value is "yes" or "nop"
data Dec (P : Set) : Set where
  yes : P     -> Dec P
  nop : Not P -> Dec P

data Pair : Set where
  pair : Nat -> Nat -> Pair

data _≤_ : Nat -> Nat -> Set where
  z≤n : ∀ {n}                 → zero   ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → succ m ≤ succ n

data Even : Nat -> Set where
  even-zero : Even 0
  even-succ : ∀ (n : Nat) -> Even n -> Even (succ (succ n))

data Odd : Nat -> Set where
  odd-one : Odd 1
  odd-succ : ∀ (n : Nat) -> Odd n -> Odd (succ (succ n))

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

not-not : ∀ (a : Bool) → a ≡ not (not a)
not-not true  = refl
not-not false = refl


or-theorem-0 : ∀ (a : Bool) -> or a (not a) ≡ true
or-theorem-0 true  = refl
or-theorem-0 false = refl

and-theorem-1 : ∀ (a : Bool) -> and a (not a) ≡ false
and-theorem-1 true  = refl
and-theorem-1 false = refl

comm-bool : ∀ (a : Bool) -> ∀ (b : Bool) -> and a b ≡ and b a
comm-bool true true = refl
comm-bool true false = refl
comm-bool false true = refl
comm-bool false false = refl

-- exemplo do https://rosettacode.org/wiki/Proof
-- comm-nat : (m n : Nat) -> m + n ≡ n + m

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



cake : ∀ (a : Bool) -> ∀ (e : a ≡ true) -> Nat
cake a e = 42

my-program-0 : ∀ (a : Bool) -> ∀ (b : Bool) -> ∀ (e : b ≡ or a (not a)) -> Nat
my-program-0 a b e =
  let before   = e                                -- b ≡ or a (not a)
      template = λ x -> b ≡ x                     -- x represent where will be substituted on "before"
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
sub zero     (succ x) = zero -- second element being bigger that the first will result a negative number

add-zero-n : ∀ (n : Nat) -> add 0 n ≡ n
add-zero-n n = refl

-- m+0≡m : (m : ℕ) → m + 0 ≡ m
-- m+0≡m 0      = refl
-- m+0≡m (1+ m) = cong (m+0≡m m)

-- +-identity′ : ∀ (n : ℕ) → n + zero ≡ n
-- +-identity′ zero = refl
-- +-identity′ (suc n) rewrite +-identity′ n = refl
add-n-zero : ∀ (n : Nat) -> add n 0 ≡ n
add-n-zero zero     = refl
add-n-zero (succ n) = cong succ (add-n-zero n)

even-6 : Even 6
even-6 = even-succ 4 (even-succ 2 (even-succ 0 even-zero))

even-14 : Even 14
even-14 = even-succ 12 (even-succ 10 (even-succ 8 (even-succ 6 (even-succ 4 (even-succ 2 (even-succ zero even-zero))))))

is-even-0 : ∀ (n : Nat) -> Bool
is-even-0 zero           = true
is-even-0 (succ zero)    = false
is-even-0 (succ(succ a)) = is-even-0 a

-- context n : Nat
-- context x : Not (Even n)
-- goal : Not (Even (succ (succ n)))
aux-is-even-1 : ∀ (n : Nat) -> (x : Not (Even n)) -> Not (Even (succ (succ n)))
aux-is-even-1 n x (even-succ .n p) = x p

one-not-even : Not (Even 1)
one-not-even = λ ()

-- What is the evidence that makes a number even?
-- Returns a Dec: Why it is "true" or why it is "false"?
is-even-1 : ∀ (n : Nat) -> Dec (Even n)
is-even-1 zero           = yes even-zero
is-even-1 (succ zero)    = nop λ ()
-- This field asks for a type Dec (Even (succ (succ n))), but a Dec can
-- return 2 values: yes or nop. "with" opens this case so we can deal
-- with both types
is-even-1 (succ(succ n))  with is-even-1 n
is-even-1 (succ (succ n)) | yes x = yes (even-succ n x) -- is even
is-even-1 (succ (succ n)) | nop x = nop (aux-is-even-1 n x)


-- Duplicates a number
double : ∀ (n : Nat) -> Nat
double zero     = zero
double (succ n) = (succ (succ (double n)))

double-is-even : ∀ (n : Nat) -> Even (double n)
double-is-even zero     = even-zero
double-is-even (succ n) = even-succ (double n) (double-is-even n)



almost-assoc : ∀ (m : Nat) -> succ (add m m) ≡ add m (succ m)
almost-assoc zero    = refl
almost-assoc (succ n) = {!   !}

-- ih2 : succ (add m m) ≡ succ (double m)
-- eqp : succ (add m m) ≡ add m (succ m)
add-n-n-double : ∀ (n : Nat) -> add n n ≡ double n -- both of them returns a Nat
add-n-n-double zero     = refl
add-n-n-double (succ m) =
  let ih  = add-n-n-double m -- working with something "concrete"
      ih2 = cong succ ih -- cong apply something on both sides of the equality
      eqp = almost-assoc m
      template = λ x -> x ≡ succ (double m)
      result = (subst template eqp ih2)
      ih3 = cong succ result
  in ih3
-- Notes --
--       add m m         ≡             double m   -- inductive hypotesis (we have it for free)
-- succ (add m m)        ≡ succ       (double m)  -- applying (cong succ)
-- succ (succ (add m m)) ≡ succ (succ (double m)) -- applying (cong succ)
-- succ (add m (succ m)) ≡ succ (succ (double m)) -- objetive




-- sub-ok : ∀ (n : Nat) -> ∀ (m : Nat) -> (mn) -> add n (sub m n) ≡ m
-- sub-ok n m = ?

-- proof that adding 2 odds is always an even




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
