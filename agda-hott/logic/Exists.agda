open import Base
open import logic.Truncation

module logic.Exists where

  -- The classical existential quantifier is recovered as a
  -- truncation.
  ∃ : ∀{ℓᵢ ℓⱼ} → (S : Type ℓᵢ) → (T : S → Type ℓⱼ) → Type (ℓᵢ ⊔ ℓⱼ)
  ∃ S T = ∥ Σ S T ∥
