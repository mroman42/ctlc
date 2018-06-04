{-# OPTIONS --without-K #-}

-- Agda-MLTT library.
-- Author: Mario Román.

-- Booleans.  An inductive type with two elements, basic operations on
-- the type, pattern-matching helpers and some lemmas.

open import Prop
open import Base

module Booleans where

-- Booleans are defined with two constructors. We need to give
-- instructions to the compiler to render them into compilable code.
data Bool : Set where
  false true : Bool
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}


-- Equality on booleans (not to be confused with equality for
-- propositions) is decidable, meaning that each boolean must be
-- either true or false.
_?? : (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
true ?? = inl refl
false ?? = inr refl


-- And function.
and : Bool → Bool → Bool
and true b = b
and false b = false

-- Proofs for some lemmas on the and function.
and-true : (b : Bool) → and b true ≡ b
and-true true = refl
and-true false = refl

and-false : (b : Bool) → and b false ≡ false
and-false true = refl
and-false false = refl

and-both : (b : Bool) → and b b ≡ b
and-both true = refl
and-both false = refl

-- Not function.
not : Bool → Bool
not true = false
not false = true

-- Proofs for some lemmas on the not function.
not-inj : (a b : Bool) → not a ≡ not b → a ≡ b
not-inj true true α = refl
not-inj true false α rewrite α = refl
not-inj false true α rewrite α = refl
not-inj false false α = refl

not-double : (a : Bool) → not (not a) ≡ a
not-double true = refl
not-double false = refl

-- XOR function
xor : Bool → Bool → Bool
xor true b = not b
xor false b = b

-- Proofs for some lemmas on the xor function.
xor-not-l : (a b : Bool) → xor (not a) b ≡ not (xor a b)
xor-not-l true b rewrite not-double b = refl
xor-not-l false b = refl

xor-not-r : (a b : Bool) → xor a (not b) ≡ not (xor a b)
xor-not-r true b = refl
xor-not-r false b = refl

xor-assoc : (a b c : Bool) → xor a (xor b c) ≡ xor (xor a b) c
xor-assoc true true true = refl
xor-assoc true true false = refl
xor-assoc true false c = refl
xor-assoc false b c = refl

xoraa : ∀ a → xor a a ≡ false
xoraa true = refl
xoraa false = refl

-- Or function.
or : Bool → Bool → Bool
or true b = true
or false b = b

-- Proofs for some lemmas on the or function.
or-rtrue : (a : Bool) → or a true ≡ true
or-rtrue true = refl
or-rtrue false = refl

or-rfalse : (a : Bool) → or a false ≡ a
or-rfalse true = refl
or-rfalse false = refl


-- True is different from false. This is directly computed by pattern
-- matching.
true≢false : ¬ (true ≡ false)
true≢false ()
