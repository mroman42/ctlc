{-# OPTIONS --without-K #-}

-- Agda-hott library.
-- Author: Mario Román

-- HLevels.  Higher levels of the homotopical structure, where the
-- first levels are Contractible types (0), Propositions (1) and Sets
-- (2). They would correspond to homotopy levels. We only work with
-- these first levels.

open import Base
open import Equality
open import EquationalReasoning
open import equality.Sigma
open import equality.FunctionExtensionality
open import logic.Contractible
open import logic.Propositions
open import logic.Sets

module logic.HLevels where

  -- Propositions are Sets.
  propIsSet : ∀{ℓ} {A : Type ℓ} → isProp A → isSet A
  propIsSet {A = A} f a _ p q = lemma p · inv (lemma q)
    where
      triang : {y z : A} {p : y == z} → (f a y) · p == f a z
      triang {p = refl b} = inv (·-runit (f a b))
      
      lemma : {y z : A} (p : y == z) → p == inv (f a y) · (f a z)
      lemma {y} {z} p = 
        begin
          p                         ==⟨ ap (_· p) (inv (·-linv (f a y))) ⟩
          inv (f a y) · f a y · p   ==⟨ ·-assoc (inv (f a y)) (f a y) p ⟩
          inv (f a y) · (f a y · p) ==⟨ ap (inv (f a y) ·_) triang ⟩
          inv (f a y) · (f a z)
        ∎
      
  -- Contractible types are Propositions.
  contrIsProp : ∀{ℓ}  {A : Type ℓ} → isContr A → isProp A
  contrIsProp (a , p) x y = inv (p x) · p y

  -- To be contractible is itself a proposition.
  isContrIsProp : ∀{ℓ}  {A : Type ℓ} → isProp (isContr A)
  isContrIsProp {_} {A} (a , p) (b , q) = Σ-bycomponents (inv (q a) , piProp (AisSet b) _ q)
    where
      AisSet : isSet A
      AisSet = propIsSet (contrIsProp (a , p))
