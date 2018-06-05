{-# OPTIONS --without-K #-}

-- Agda-hott library.
-- Author: Mario Román

-- Composition.  Properties of function composition.

open import Base
open import Equality

module Composition where
  -- Associativity
  ∘-lassoc : ∀{ℓ} {A B C D : Type ℓ} →
    (h : C → D) → (g : B → C) → (f : A → B) →
    (h ∘ (g ∘ f)) == ((h ∘ g) ∘ f)
  ∘-lassoc h g f = refl (λ x → h (g (f x)))

  ∘-rassoc : ∀{ℓ} {A B C D : Type ℓ} →
    (h : C → D) → (g : B → C) → (f : A → B) →
    ((h ∘ g) ∘ f) == (h ∘ (g ∘ f))
  ∘-rassoc h g f = inv (∘-lassoc h g f)
