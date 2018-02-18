{-# OPTIONS --without-K #-}

open import Base
open import Equality
open import equivalence.EquivalenceSet
open import algebra.Groups

module topology.FundamentalGroup where

  Ω : ∀{ℓ} (A : Type ℓ) → (a : A) → Type ℓ
  Ω A a = (a == a)

  Ω-st : ∀{ℓ} (A : Type ℓ) → (a : A) → GroupStructure (Ω A a)
  Ω-st A a = group-structure _·_ (refl a)
    (λ a → inv (·-lunit a)) (λ a → inv (·-runit a))
    (λ x y z → inv (·-assoc x y z))
    inv ·-rinv ·-linv

  Ω-gr : ∀{ℓ} (A : Type ℓ) → (a : A) → Group {ℓ}
  Ω-gr A a = group (a == a) (Ω-st A a)

  Ω-st-r : ∀{ℓ} (A : Type ℓ) → (a : A) → GroupStructure (Ω A a)
  Ω-st-r A a = group-structure (λ x y → y · x) (refl a)
    (λ a → inv (·-runit a)) (λ a → inv (·-lunit a))
    (λ x y z → ·-assoc z y x)
    inv ·-linv ·-rinv
  
