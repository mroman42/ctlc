{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality
open import Homotopies
open import Composition
open import logic.Contractible
open import logic.Propositions
open import equality.Sigma
open import equivalence.Equivalence

module equivalence.Quasiinverses where
  
  module Invertibles {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where
    -- Definitions for quasiinverses, left-inverses, right-inverses and
    -- biinverses.
    qinv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
    qinv f = Σ (B → A) (λ g → ((f ∘ g) ∼ id) × ((g ∘ f) ∼ id)) 
  
    linv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
    linv f = Σ (B → A) (λ g → (g ∘ f) ∼ id)
  
    rinv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
    rinv f = Σ (B → A) λ g → (f ∘ g) ∼ id
  
    biinv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
    biinv f = linv f × rinv f

    qinv-biinv : (f : A → B) → qinv f → biinv f
    qinv-biinv f (g , (u1 , u2)) = (g , u2) , (g , u1)

    biinv-qinv : (f : A → B) → biinv f → qinv f
    biinv-qinv f ((h , α) , (g , β)) = g , (β , δ)
      where
        γ1 : g ∼ ((h ∘ f) ∘ g)
        γ1 = rcomp-∼ g (h-simm (h ∘ f) id α)
  
        γ2 : ((h ∘ f) ∘ g) ∼ (h ∘ (f ∘ g))
        γ2 x = refl (h (f (g x)))

        γ : g ∼ h
        γ = γ1 ● (γ2 ● (lcomp-∼ h β))

        δ : (g ∘ f) ∼ id
        δ = (rcomp-∼ f γ) ● α

    -- TODO: Propositions
    -- linvIsProp : (f : A → B) → isProp (linv f)
    -- linvIsProp f = {!!}
  open Invertibles public

  module QuasiinversesAndEquivalences {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where
    equiv-biinv : (f : A → B) → isContrMap f → biinv f
    equiv-biinv f contrf = (remap eq , rlmap-inverse-h eq) , (remap eq , lrmap-inverse-h eq)
      where
        eq : A ≃ B
        eq = f , contrf
  
    qinv-equiv : ∀{ℓ}  {A B : Type ℓ} → (f : A → B) → qinv f → isContrMap f
    qinv-equiv f (g , (α , β)) b = ((g b) , α b) , {!!}
      where
        uniq : (x : fib f b) → (g b , α b) == x
        uniq (a , p) = Σ-bycomponents ((ap g (inv p) · β a) , {!!})
  
    biinv-equiv : ∀{ℓ}  {A B : Type ℓ} → (f : A → B) → biinv f → isContrMap f
    biinv-equiv f ((gl , hgl) , (gr , hgr)) = λ b → {!!}
