{-# OPTIONS --without-K #-}

-- Agda-hott library.
-- Author: Mario Román

-- EquivalenceComposition.  Composition of equivalences and properties
-- of that composition.

open import Agda.Primitive
open import Base
open import Equality
open import EquationalReasoning
open import Composition
open import Homotopies
open import logic.Contractible
open import equivalence.Equivalence
open import equivalence.EquivalenceProp
open import equivalence.Quasiinverses
open import equality.FunctionExtensionality

module equivalence.EquivalenceComposition where

  -- Composition of quasiinverses
  qinv-comp : ∀{ℓ} {A B C : Type ℓ} → Σ (A → B) qinv → Σ (B → C) qinv → Σ (A → C) qinv
  qinv-comp (f , (if , (εf , ηf))) (g , (ig , (εg , ηg))) = (g ∘ f) , ((if ∘ ig) ,
      ( (λ x → ap g (εf (ig x)) · εg x)
      ,  λ x → ap if (ηg (f x)) · ηf x))

  qinv-inv : ∀{ℓ} {A B : Type ℓ} → Σ (A → B) qinv → Σ (B → A) qinv
  qinv-inv (f , (g , (ε , η))) = g , (f , (η , ε))

  -- Composition of equivalences
  idEqv : ∀{ℓ} {A : Type ℓ} → A ≃ A
  idEqv = id , λ a → (a , refl a) , λ { (_ , refl _) → refl (a , refl a) }

  compEqv : ∀{ℓ} {A B C : Type ℓ} → A ≃ B → B ≃ C → A ≃ C
  compEqv {ℓ} {A} {B} {C} eqf eqg = qinv-≃ (fst qcomp) (snd qcomp)
    where
      qcomp : Σ (A → C) qinv
      qcomp = qinv-comp (≃-qinv eqf) (≃-qinv eqg)

  invEqv : ∀{ℓ} {A B : Type ℓ} → A ≃ B → B ≃ A
  invEqv {ℓ} {A} {B} eqf = qinv-≃ (fst qcinv) (snd qcinv)
    where
      qcinv : Σ (B → A) qinv
      qcinv = qinv-inv (≃-qinv eqf)

  -- Lemmas about composition
  compEqv-inv : ∀{ℓ} {A B : Type ℓ} → (α : A ≃ B) → compEqv α (invEqv α) == idEqv
  compEqv-inv {_} {A} {B} α = sameEqv (
    begin
      fst (compEqv α (invEqv α)) ==⟨ refl _ ⟩
      fst (invEqv α) ∘ fst α     ==⟨ funext (rlmap-inverse-h α) ⟩
      id
    ∎)

