{-# OPTIONS --without-K #-}

open import Base
open import Equality
open import Homotopies
open import Composition
open import logic.Propositions
open import equivalence.Equivalence

module equivalence.Quasiinverses where
  
  module Invertibles {ℓ} {A B : Type ℓ} where
    -- Definitions for quasiinverses, left-inverses, right-inverses and
    -- biinverses.
    qinv : (A → B) → Type ℓ
    qinv f = Σ (B → A) (λ g → ((f ∘ g) ∼ id) × ((g ∘ f) ∼ id)) 
  
    linv : (A → B) → Type ℓ
    linv f = Σ (B → A) (λ g → (g ∘ f) ∼ id)
  
    rinv : (A → B) → Type ℓ
    rinv f = Σ (B → A) λ g → (f ∘ g) ∼ id
  
    biinv : (A → B) → Type ℓ
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

    -- Propositions
    linvIsProp : (f : A → B) → isProp (linv f)
    linvIsProp f = {!!}
  open Invertibles public

  equiv-biinv : ∀{ℓ}  (A B : Type ℓ) → (f : A → B) → isContrMap f → biinv f
  equiv-biinv A B f contrf = (remap eq , rlmap-inverse-h eq) , (remap eq , lrmap-inverse-h eq)
    where
      eq : A ≃ B
      eq = f , contrf

  biinv-equiv : ∀{ℓ}  (A B : Type ℓ) → (f : A → B) → biinv f → isContrMap f
  biinv-equiv A B f biinvf = {!!}
