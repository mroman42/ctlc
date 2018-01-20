{-# OPTIONS --without-K #-}

open import Base
open import Equality

module logic.Contractible where

  -- Contractible types. A contractible type is a type such that every
  -- element is equal to a center of contraction.
  isContr : ∀{ℓ}  (A : Type ℓ) → Type ℓ
  isContr A = Σ A (λ a → ((x : A) → a == x))

  
  -- The fiber of a map over a point is given by
  fib : ∀{ℓ} {A B : Type ℓ}  (f : A → B) → B → Type ℓ
  fib {A = A} f b = Σ A (λ a → f a == b)
