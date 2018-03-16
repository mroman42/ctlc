{-# OPTIONS --without-K #-}

open import base.Universes

module base.Empty where

  -- A datatype without constructors is the empty type.
  data ⊥ {ℓᵢ} : Type ℓᵢ where

  -- Ex falso quodlibet
  exfalso : ∀{ℓ ℓᵢ} {A : Type ℓ} → ⊥ {ℓᵢ} → A
  exfalso ()

  -- Negation
  ¬ : ∀{ℓ} → Type ℓ → Type ℓ
  ¬ A = (A → ⊥ {lzero})
