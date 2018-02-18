{-# OPTIONS --rewriting --type-in-type #-}

open import Base
open import Dyadic
open import Prop

module Reals where

  record ℝ : Set where
    constructor real
    field
      -- Dedekind cuts are
      lower : Dyadic → Prop
      upper : Dyadic → Prop

      -- Inhabited
      lhabit : Prf (∃ Dyadic lower)
      uhabit : Prf (∃ Dyadic upper)

      -- Rounded
      lround : Prf (Forall Dyadic (λ q → lower q <~> ∃ Dyadic (λ r → (q <ᵈ r) ∧ lower r)))
      uround : Prf (Forall Dyadic (λ q → upper q <~> ∃ Dyadic (λ r → (r <ᵈ q) ∧ upper r)))

      -- Disjoint
      disjoint : Prf (Forall Dyadic (λ q → Not (lower q ∧ upper q)))

      -- Located
      located : Prf (Forall Dyadic (λ q → Forall Dyadic (λ r → (q <ᵈ r) ~> (lower q ∨ upper r))))
  open ℝ public

  zeroᴿ : ℝ
  zeroᴿ = real
    (λ d → d <ᵈ zeroᵈ)
    (λ d → zeroᵈ <ᵈ d)
    ∣ (-ᵈ oneᵈ) , ** ∣
    ∣ oneᵈ , ** ∣
    (λ d → (λ eq → ∣ (1/2ᵈ *ᵈ d) , ({!!} , {!!}) ∣) , {!!})
    {!!}
    {!!}
    {!!}

    
