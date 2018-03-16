{-# OPTIONS --without-K #-}
{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Base
open import Equality
open import logic.SetTruncation
open import logic.SetTruncationLemmas
open import logic.HLevels
open import equivalence.EquivalenceSet
open import algebra.Groups
open import algebra.HigherGroups

module topology.FundamentalHigherGroup where

  Ω : ∀{ℓ} (A : Type ℓ) → (a : A) → Type ℓ
  Ω A a = (a == a)

  Ω-st : ∀{ℓ} (A : Type ℓ) → (a : A) → HigherGroupStructure (Ω A a)
  Ω-st A a = higher-group-structure _·_ (refl a)
    (λ a → inv (·-lunit a)) (λ a → inv (·-runit a))
    (λ x y z → inv (·-assoc x y z))
    inv ·-rinv ·-linv

  Ω-st-r : ∀{ℓ} (A : Type ℓ) → (a : A) → HigherGroupStructure (Ω A a)
  Ω-st-r A a = higher-group-structure (λ x y → y · x) (refl a)
    (λ a → inv (·-runit a)) (λ a → inv (·-lunit a))
    (λ x y z → ·-assoc z y x)
    inv ·-linv ·-rinv
