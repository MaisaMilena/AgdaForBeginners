-- 1
-- 10
-- 11
-- 100
-- 101
-- 110
-- 111
-- 1000
-- 1001
-- 1010
-- 1011
-- 1100
-- 1101
-- 1110
-- 1111
-- 10000

module StartingSimple where

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

-- Give the opposite value of a Bool
not : ∀ (bool : Bool) -> Bool
not true  = false
not false = true

-- Flip bits. Transforms 0 in 1 and 1 in 0
flip : ∀ (bin : Bin) -> Bin
flip be       = be
flip (b0 bin) = b1 (flip bin)
flip (b1 bin) = b0 (flip bin)

-- Count the number of 1 in a binary
count-ones : ∀ (bin : Bin) -> Nat
count-ones be       = zero
count-ones (b0 bin) = (count-ones bin)
count-ones (b1 bin) = succ (count-ones bin)

-- Increments a binary
inc : ∀ (bin : Bin) -> Bin
inc be       = be
inc (b0 bin) = b1 (bin)
inc (b1 bin) = b0 (inc bin)

-- Add two natural numbers
add : ∀ (n : Nat) -> ∀ (m : Nat) -> Nat
add zero      m     = m
add (succ n)  m     = succ (add n m)

-- Add two binary numbers
addBin : Bin -> Bin -> Bool -> Bin
addBin be be true             = b1 (be)
addBin be be false            = be
addBin be (b0 m) true         = b1 (addBin be m false)
addBin be (b0 m) false        = b0 (addBin be m false)
addBin be (b1 m) true         = b1 (addBin be m false)
addBin be (b1 m) false        = b1 (addBin be m false)
addBin (b0 n) be true         = b1 (addBin n be false)
addBin (b0 n) be false        = b0 (addBin n be false)
addBin (b0 n) (b0 m) true     = b1 (addBin n m false)
addBin (b0 n) (b0 m) false    = b0 (addBin n m false)
addBin (b0 n) (b1 m) true     = b1 (addBin n m false)
addBin (b0 n) (b1 m) false    = b1 (addBin n m false)
addBin (b1 n) be true         = b1 (addBin n be false)
addBin (b1 n) be false        = b1 (addBin n be false)
addBin (b1 n) (b0 m) true     = b1 (addBin n m false)
addBin (b1 n) (b0 m) false    = b1 (addBin n m false)
addBin (b1 n) (b1 m) true     = b1 (addBin n m true)
addBin (b1 n) (b1 m) false    = b0 (addBin n m true)
-- Optimized
addBin2 : Bin -> Bin -> Bin
addBin2 be     m      = m
addBin2 n      be     = n
addBin2 (b0 n) (b0 m) = b0 (addBin2 n m)
addBin2 (b1 n) (b0 m) = b1 (addBin2 n m)
addBin2 (b0 n) (b1 m) = b1 (addBin2 n m)
addBin2 (b1 n) (b1 m) = b0 (inc (addBin2 n m))

-- Check if an string is equal to another
eqString : ∀ (str : Bin) -> (oth : Bin) -> Bool
eqString be       be       = true
eqString (b0 str) (b0 oth) = eqString str oth
eqString (b1 str) (b1 oth) = eqString str oth
eqString a        b        = false

-- Check if a binary starts with a pattern
startsWith : ∀ (pat : Bin) -> ∀ (str : Bin) -> Bool
startsWith (b0 pat) (b0 str)  = (startsWith pat str)
startsWith (b1 pat) (b1 str)  = (startsWith pat str)
startsWith be       n         = true
startsWith m        n         = false

or : ∀ (first : Bool) -> ∀ (second : Bool) -> Bool
or true  n     = true
or false m     = m

-- Check if a binary contains a pattern
find : ∀ (str : Bin) -> ∀ (bin : Bin) -> Bool
find str  be        = (startsWith str be)
find str  (b0 bin)  = (or (startsWith str (b0 bin)) (find str bin))
find str  (b1 bin)  = (or (startsWith str (b1 bin)) (find str bin))



-- TESTS --
notTest : Bool
notTest = not (false)

isEqualTest : Bool
isEqualTest = (eqString (b1(b0(b1(b1 be)))) (b1(b0(b1 be))))

startsWithTest : Bool
startsWithTest = (startsWith (b1(b0(b1 be))) (b1(b0(b1(b1(b0(b0 be)))))))

findTest : Bool
findTest = (find (b1(b0(b1(b1(b0(b0 be)))))) (b1(b0(b1(b1(b0(b0 be)))))))
findTest2 : Bool
findTest2 = (find be be)
