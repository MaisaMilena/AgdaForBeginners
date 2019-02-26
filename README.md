# Agda For Beginners

Here are some examples that I'm using to learn functional programming and develop Formal Proofs using Agda as the proof assistant.

### Starting Simple
- Exploring notation of booleans, natural numbers and binary
- Add two numbers (natural and binary)
- Incrementing boolean
- Find patterns in binary numbers

### Equality
Equalities are defined between objects of the same type. Two objects are equal if we have a proof of their equality.
In Agda, we can represent this by means of a function which takes two instances of some type M, and maps this to a proof of equality.
- Data types: ``Dec, Odd, Even, Empty, Not``
- Receiving 2 booleans ``a`` and ``b`` and a proof that ``a`` is true, proof that ``and a b`` is true
- Given a Bool ``b`` proof that ``not(not b) ≡ b ``
- Commutation: proof that ``add a b ≡ add b a``
- De Morgan's law: ``not (and a b) ≡ or (not a) (not b)``
- Given 2 booleans ``a`` and ``b`` and a proof that ``∀ (e : b ≡ or a (not a))`` returns a ``Nat``
- Subtraction of ``Nat``
- Adding ``Even`` numbers
- Proving that a number is ``Even``
- Proof that doubling a number results in an ``Even`` number

### Notes
- reflexivity: ``refl : ∀ {r} -> (r == r)``
- symmetry: ``sym : ∀ {r s} -> (r == s) -> (s == r)``
- transitivity: ``trans : ∀ {r s t} -> (r == s) -> (s == t) -> (r == t)``
- congruency: ``cong : ∀ {A B} {m n : A} -> (f : A -> B) -> m ≡ n -> f m ≡ f n``
  A relation is said to be a congruence for a given function if it is preserved by applying that function.
If ``e`` is evidence that ``x ≡ y``, then ``cong f e`` is evidence that ``f x ≡ f y``, for any function ``f``.
- associativity: ``assoc : ∀ a b c -> a + (b + c) ≡ (a + b) + c``

-- TODO: write about implicit arguments 
