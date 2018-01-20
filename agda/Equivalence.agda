{-# OPTIONS --without-K #-}

open import Base
open import Equality
open import logic.Contractible

module Equivalence where

  -- Contractible maps. A map is contractible if the fiber in any
  -- point is contractible, that is, each element has a unique
  -- preimage.
  isContrMap : ∀{ℓ}  {A B : Type ℓ} → (f : A → B) → Type ℓ 
  isContrMap {_} {A} {B} f = (b : B) → isContr (fib f b)

  -- There exists an equivalence between two types if there exists a
  -- contractible function between them.
  isEquiv : ∀{ℓ}  {A B : Type ℓ} → (f : A → B) → Type ℓ
  isEquiv = isContrMap

  -- Equivalence of types.
  _≃_ : ∀{ℓ}  (A B : Type ℓ) → Type ℓ
  A ≃ B = Σ (A → B) isEquiv
