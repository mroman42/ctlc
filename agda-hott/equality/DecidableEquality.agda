{-# OPTIONS --without-K #-}

-- Agda-hott library.
-- Author: Mario Román

-- DecidableEquality.  A type has decidable equality if any two of its
-- elements are equal or different. This would be a particular
-- instance of the Law of Excluded Middle that holds even if we do not
-- assume Excluded Middle.

open import Agda.Primitive
open import Base
open import Equality
open import equality.CartesianProduct

module equality.DecidableEquality {ℓ} where

  -- A type has decidable equality if we can prove that any two of its
  -- elements are equal or different.
  decEq : (A : Type ℓ) → Type ℓ
  decEq A = (a b : A) → (a == b) + ¬ (a == b)

  -- The product of types with decidable equality is a type with
  -- decidable equality.
  decEqProd : {A B : Type ℓ} → decEq A → decEq B → decEq (A × B)
  decEqProd da db (a1 , b1) (a2 , b2) with (da a1 a2) | (db b1 b2)
  decEqProd da db (a1 , b1) (a2 , b2) | inl aeq | inl beq = inl (prodByComponents (aeq , beq))
  decEqProd da db (a1 , b1) (a2 , b2) | inl aeq | inr bnq = inr λ b → bnq (ap snd b)
  decEqProd da db (a1 , b1) (a2 , b2) | inr anq | u       = inr λ b → anq (ap fst b)

