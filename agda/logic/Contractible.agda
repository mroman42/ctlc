{-# OPTIONS --without-K #-}

open import Base
open import Equality

module logic.Contractible where

  -- Contractible types. A contractible type is a type such that every
  -- element is equal to a center of contraction.
  isContr : ∀{ℓ}  (A : Type ℓ) → Type ℓ
  isContr A = Σ A (λ a → ((x : A) → a == x))

  
  
