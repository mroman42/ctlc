{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality

module logic.Propositions where

  -- A type is a mere proposition if any two inhabitants of the type
  -- are equal
  isProp : ∀{ℓ}  (A : Type ℓ) → Type ℓ
  isProp A = ((x y : A) → x == y)

  -- The type of mere propositions
  hProp : ∀{ℓ} → Type (lsuc ℓ)
  hProp {ℓ} = Σ (Type ℓ) id
  
  -- TODO: Truth is the only true mere proposition, any other true
  -- proposition is equivalent to truth.
  
  
  
