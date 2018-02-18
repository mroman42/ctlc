{-# OPTIONS --without-K #-}

open import base.Universes

module base.Empty {ℓ} where

  -- Agda allows datatype declarations and record types.
  -- A datatype without constructors is the empty type.
  data ⊥ : Type ℓ where

  -- Negation
  ¬ : ∀{ℓᵢ} → Type ℓᵢ → Type (ℓᵢ ⊔ ℓ)
  ¬ A = (A → ⊥)

  -- Ex falso quodlibet
  exfalso : ∀{ℓᵢ} {A : Type ℓᵢ} → ⊥ → A
  exfalso ()
