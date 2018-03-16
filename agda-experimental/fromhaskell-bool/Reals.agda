module Reals where

open import base.Base
open import base.Prop
open import SageRationals

-- Hay forma de ahorrarse trabajar con el módulo Prop?
-- Y de paso ahorrarse type-in-type
-- Solo usando ∃ y ∨, y comprobando irrelevancia de lower y upper



-- TODO
--  1. Positive reals.
--  0! Rationals! whose predicates cannot depend on construction. (prelude?)
--  2. Decidable equalities on rationals
--  3. that rewrite to equalities on natural numbers
--  4. provable using prelude tactics.
--  5. IsProp-based propositions, without --type-in-type.
--  6. Definition of * is easy (???) in positive reals.
--  7. Check that the square root of 2 is in fact a square root.
--  8. Computable digits of the square root using rationals.


record ℝ : Set₁ where
  field
    -- Dedekind cuts are
    lower : ℚ → Set
    upper : ℚ → Set
  
    -- Propositional
    lprop : (q : ℚ) → isProp (lower q)
    uprop : (q : ℚ) → isProp (upper q)

    -- Inhabited
    lhabit : ∃ ℚ lower
    uhabit : ∃ ℚ upper

    -- Rounded
    lround-1 : (q : ℚ) → lower q → ∃ ℚ (λ r → ((q <ᵣ r) ≡ true) × lower r)
    lround-2 : (q : ℚ) → ∃ ℚ (λ r → ((q <ᵣ r) ≡ true) × lower r) → lower q
    uround-1 : (q : ℚ) → upper q → ∃ ℚ (λ r → ((r <ᵣ q) ≡ true) × upper r)
    uround-2 : (q : ℚ) → ∃ ℚ (λ r → ((q <ᵣ r) ≡ true) × upper r) → upper q

    -- Disjoint
    disjoint : (q : ℚ) → ¬ (lower q × upper q)

    -- Located
    located : (q r : ℚ) → ((q <ᵣ r) ≡ true) → (lower q ∨ upper r)
open ℝ public

postulate
  ASSUME : {A : Set} → A


real0 : ℝ
real0 = record
  { lower = λ x → x <ᵣ (0 % 1) ≡ true
  ; upper = λ x → (0 % 1) <ᵣ x ≡ true
  ; lprop = λ q → uip
  ; uprop = λ q → uip
  ; lhabit = (-ᵣ (1 % 1))  ,, ASSUME
  ; uhabit = (1 % 1) ,, ASSUME
  ; lround-1 = λ q p → (q *ᵣ (1 % 2)) ,, (ASSUME , ASSUME)
  ; lround-2 = λ q x → ∃-elim x uip (λ { (r , (α , β)) → ASSUME })
  ; uround-1 = λ q x → (q *ᵣ (1 % 2)) ,, (ASSUME , ASSUME)
  ; uround-2 = λ q x → ∃-elim x uip λ { (r , (α , β)) → ASSUME }
  ; disjoint = λ q x → ASSUME  -- Absurds from Assume
  ; located = λ q r x → ASSUME 
  }


sqrt2 : ℝ
sqrt2 = record
  { lower = λ x → ((x *ᵣ x) <ᵣ (2 % 1)) ≡ true
  ; upper = λ x → ((2 % 1) <ᵣ (x *ᵣ x)) ≡ true
  ; lprop = λ q → uip
  ; uprop = λ q → uip
  ; lhabit = (0 % 1) ,, ASSUME
  ; uhabit = (2 % 1) ,, ASSUME
  ; lround-1 = λ q x → {!!}
  ; lround-2 = λ q x → {!!}
  ; uround-1 = λ q x → {!!}
  ; uround-2 = λ q x → {!!}
  ; disjoint = λ q x → ASSUME
  ; located = λ q r x → ASSUME -- Half
  }

_+r_ : ℝ → ℝ → ℝ
a +r b = record
  { lower = λ q → ∃ ℚ λ r → ∃ ℚ λ s → (lower a r × lower b s) × (((r +ᵣ s) ==ᵣ q) ≡ true)
  ; upper = λ q → ∃ ℚ λ r → ∃ ℚ λ s → (upper a r × upper b s) × (((r +ᵣ s) ==ᵣ q) ≡ true)
  ; lprop = λ q → ∃-isProp
  ; uprop = λ q → ∃-isProp
  ; lhabit =
      ∃-elim (lhabit a) ∃-isProp (λ { (u , α) →
      ∃-elim (lhabit b) ∃-isProp (λ { (v , β) →
        (u +ᵣ v) ,, (u ,, (v ,, ((α , β) , ASSUME))) 
      })})
  ; uhabit =
      ∃-elim (uhabit a) ∃-isProp (λ { (u , α) →
      ∃-elim (uhabit b) ∃-isProp (λ { (v , β) →
        (u +ᵣ v) ,, (u ,, (v ,, ((α , β) , ASSUME))) 
      })})     
  ; lround-1 = λ q x →
      ∃-elim x ∃-isProp (λ { (u , α) →
      ∃-elim α ∃-isProp (λ { (v , ((α₁ , α₂) , γ)) →
      ∃-elim (lround-1 a u α₁) ∃-isProp (λ { (l₁ , β₁) →
      ∃-elim (lround-1 b v α₂) ∃-isProp (λ { (l₂ , β₂) →
        (l₁ +ᵣ l₂) ,, (ASSUME , (l₁ ,, (l₂ ,, ((snd β₁ , snd β₂) , ASSUME))))
      })})})})
  ; lround-2 = λ q x → ASSUME  
  ; uround-1 = λ q x → ASSUME
  ; uround-2 = λ q x → ASSUME
  ; disjoint = λ q x → ASSUME
  ; located = λ q r x → ASSUME
  }
  where
    
