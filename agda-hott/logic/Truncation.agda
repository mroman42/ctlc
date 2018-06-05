{-# OPTIONS --without-K #-}


-- Agda-hott library.
-- Author: Mario Román

-- Truncation.  Propositional truncation of types. It works as an
-- adjoint, this is shared code with the Agda-mltt library.

open import Base
open import Equality
open import logic.Propositions

module logic.Truncation where

  private
    -- Higher inductive type, defined with equalities between any two
    -- members.
    data !∥_∥ {ℓ} (A : Type ℓ) : Type ℓ where
      !∣_∣ : A → !∥ A ∥

  ∥_∥ : ∀{ℓ} (A : Type ℓ) → Type ℓ
  ∥ A ∥ = !∥ A ∥

  ∣_∣ : ∀{ℓ} {X : Type ℓ} → X → ∥ X ∥
  ∣ x ∣ = !∣ x ∣

  -- Any two elements of the truncated type are equal
  postulate trunc : ∀{ℓ} {A : Type ℓ} → isProp ∥ A ∥

  -- Recursion principle
  trunc-rec : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : Type ℓⱼ} → isProp P → (A → P) → ∥ A ∥ → P
  trunc-rec _ f !∣ x ∣ = f x
