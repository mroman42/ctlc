{-# OPTIONS --without-K #-}

-- Agda-hott library.
-- Author: Mario Román

-- Sets.  Sets are types without any higher dimensional structure, all
-- parallel paths are homotopic and the homotopy is given by a
-- continuous function on the two paths.

open import Base
open import Equality
open import EquationalReasoning
open import logic.Propositions
open import equality.FunctionExtensionality
open import equality.CartesianProduct


module logic.Sets where

  -- A type is a "set" by definition if any two equalities on the type
  -- are equal.
  isSet : ∀{ℓ}  (A : Type ℓ) → Type ℓ
  isSet A = (x y : A) → isProp (x == y)

  -- The type of sets.
  hSet : ∀{ℓ} → Type (lsuc ℓ)
  hSet {ℓ} = Σ (Type ℓ) isSet

  -- Product of sets is a set.
  isSet-prod : ∀{ℓᵢ ℓⱼ}  {A : Type ℓᵢ} → {B : Type ℓⱼ}
             → isSet A → isSet B → isSet (A × B)
  isSet-prod sa sb (a , b) (c , d) p q = begin
     p                                       ==⟨ inv (prodByCompInverse p) ⟩
     prodByComponents (prodComponentwise p)  ==⟨ ap prodByComponents (prodByComponents (sa a c _ _ , sb b d _ _)) ⟩
     prodByComponents (prodComponentwise q)  ==⟨ prodByCompInverse q ⟩
     q
    ∎
