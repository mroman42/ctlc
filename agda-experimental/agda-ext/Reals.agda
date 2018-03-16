{-# OPTIONS --rewriting --type-in-type #-}

open import Base
open import Equality
open import dyadics.Dyadics
open import Prop
open import Bool

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
      lround : Prf (Forall Dyadic (λ q → lower q <~> ∃ Dyadic (λ r → [ q <ᵈ r ] ∧ lower r)))
      uround : Prf (Forall Dyadic (λ q → upper q <~> ∃ Dyadic (λ r → [ r <ᵈ q ] ∧ upper r)))

      -- Disjoint
      disjoint : Prf (Forall Dyadic (λ q → Not (lower q ∧ upper q)))

      -- Located
      located : Prf (Forall Dyadic (λ q → Forall Dyadic (λ r → [ q <ᵈ r ] ~> (lower q ∨ upper r))))
  open ℝ public

  -- zero : ℝ
  -- zero = real
  --   -- Cuts
  --   ((λ d → [ d <ᵈ 0,0ᵈ ])) ((λ d → [ 0,0ᵈ <ᵈ d ]))
  --   -- Inhabited
  --   (∣ - 1,0 , refl ∣)
  --   (∣ 1,0 , refl ∣)
  --   -- Rounded
  --   (λ d →
  --     (λ eq → ∣ halfᵈ d , ({!!} , {!!}) ∣) ,
  --     (λ hf → {!!}))
  --   (λ d →
  --     (λ eq → ∣ halfᵈ d , ({!!} , eq) ∣) ,
  --     (λ hf → {!!}))
  --   -- Disjoint
  --   (λ d → {!!})
  --   -- Located
  --   (λ d d' → {!!})

  -- one : ℝ
  -- one = real {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}

  DtoR : Dyadic → ℝ
  DtoR d = real
    -- Cuts
    (λ e → [ e <ᵈ d ])
    (λ e → [ d <ᵈ e ])
    -- Inhabited
    (∣ {!!} , {!!} ∣)
    (∣ (1,0 +ᵈ d) , refl ∣)
    -- Rounded
    (λ e →
      (λ eq → ∣ mean d e , {!!} ∣) ,
      (trec {P = [ e <ᵈ d ]} λ { (r , pr) → {!!} }))
    {!!}
    -- Disjoint
    {!!}
    -- Located
    {!!}

--   zeroᴿ : ℝ
--   zeroᴿ = real
--     (λ d → d <ᵈ zeroᵈ)
--     (λ d → zeroᵈ <ᵈ d)
--     ∣ (-ᵈ oneᵈ) , ** ∣
--     ∣ oneᵈ , ** ∣
--     (λ d → (λ eq → ∣ (1/2ᵈ *ᵈ d) , ({!!} , {!!}) ∣) , {!!})
--     {!!}
--     {!!}
--     {!!}
-- x
    
