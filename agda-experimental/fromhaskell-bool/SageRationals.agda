module SageRationals where

open import base.Base
open import base.Prop

nonzero : Nat → Set
nonzero zero = ⊥
nonzero (suc n) = ⊤

postulate
  ℚ : Set
  _%_ : Nat → (n : Nat) → {check : nonzero n} → ℚ
  _+ᵣ_ : ℚ → ℚ → ℚ
  _*ᵣ_ : ℚ → ℚ → ℚ
  -ᵣ_ : ℚ → ℚ
  inv : ℚ → ℚ
  _<ᵣ_ : ℚ → ℚ → Bool
  _==ᵣ_ : ℚ → ℚ → Bool


  
