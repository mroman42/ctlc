{-# OPTIONS --without-K #-}

-- Agda-hott library.
-- Author: Mario Román

-- EquivalenceProp.  Equivalence of two types is a
-- proposition. Moreover, equivalences preserve propositions.

open import Agda.Primitive
open import Base
open import Equality
open import EquationalReasoning
open import Composition
open import Homotopies
open import equality.Sigma
open import logic.Contractible
open import logic.Propositions
open import logic.Sets
open import logic.HLevels
open import equivalence.Equivalence

module equivalence.EquivalenceProp {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

  -- Contractible maps are propositions
  isContrMapIsProp : (f : A → B) → isProp (isContrMap f)
  isContrMapIsProp f = piProp λ a → isContrIsProp

  isEquivIsProp : (f : A → B) → isProp (isEquiv f)
  isEquivIsProp = isContrMapIsProp

  -- Equality of same-morphism equivalences
  sameEqv : {α β : A ≃ B} → fst α == fst β → α == β
  sameEqv {(f , σ)} {(g , τ)} p = Σ-bycomponents (p , (isEquivIsProp g _ τ))

  -- Equivalences preserve propositions
  isProp-≃ : (A ≃ B) → isProp A → isProp B
  isProp-≃ eq prop x y = 
    begin
      x                       ==⟨ inv (lrmap-inverse eq) ⟩
      lemap eq ((remap eq) x) ==⟨ ap (λ u → lemap eq u) (prop _ _) ⟩
      lemap eq ((remap eq) y) ==⟨ lrmap-inverse eq ⟩
      y
    ∎

  
