{-# OPTIONS --without-K #-}

open import Base
open import Equality
open import Homotopies
open import logic.Propositions

module Quasiinverses where

  -- Definitions for quasiinverses, left-inverses, right-inverses and
  -- biinverses.
  module Invertible {ℓ} {A B : Type ℓ} where
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


    -- TODO: linv and rinv are propositions
    -- linvIsProp : (f : A → B) → isProp (linv f)
    -- linvIsProp f = {!!}
  open Invertible public


