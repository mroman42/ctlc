{-# OPTIONS --without-K #-}


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
open import equality.FunctionExtensionality
open import equivalence.Equivalence
open import equivalence.EquivalenceComposition
open import equivalence.EquivalenceProp

module equivalence.EquivalenceSet where

  piSet : ∀{ℓᵢ ℓⱼ} → {A : Type ℓᵢ} → {B : A → Type ℓⱼ}
        → ((a : A) → isSet (B a)) → isSet ((a : A) → B a)
  piSet α f g = lemma
    where
      lemma : isProp (f == g)
      lemma = isProp-≃ (invEqv eqFunExt) (piProp λ a → α a (f a) (g a))
