module Reals where

open import base.Base
open import base.Prop
open import SageRationals

-- Hay forma de ahorrarse trabajar con el módulo Prop?
-- Y de paso ahorrarse type-in-type
-- Solo usando ∃ y ∨, y comprobando irrelevancia de lower y upper

record ℝ : Set where
  field
    -- Dedekind cuts are
    lower : ℚ → Prop
    upper : ℚ → Prop

    -- Inhabited
    lhabit : Prf (∃ ℚ lower)
    uhabit : Prf (∃ ℚ upper)

    -- Rounded
    lround : Prf (Forall ℚ (λ q → lower q <~> ∃ ℚ (λ r → (q <ᵣ r) ∧ lower r)))
    uround : Prf (Forall ℚ (λ q → upper q <~> ∃ ℚ (λ r → (r <ᵣ q) ∧ upper r)))

    -- Disjoint
    disjoint : Prf (Forall ℚ (λ q → Not (lower q ∧ upper q)))

    -- Located
    located : Prf (Forall ℚ (λ q → Forall ℚ (λ r → (q <ᵣ r) ~> (lower q ∨ upper r))))
open ℝ public

postulate
  ASSUME : {A : Set} → A


-- real0 : ℝ
-- real0 = real
--   -- Definition
--   (λ x → x <ᵣ (0 % 1))
--   (λ x → (0 % 1) <ᵣ x)
--   -- Inhabited
--   ∣ (-ᵣ (1 % 1)) , ASSUME ∣
--   ∣ (1 % 1) , ASSUME ∣
--   -- Rounded
--   ( λ q →
--     (λ lq → ∣ (q *ᵣ (1 % 2)) , (ASSUME , ASSUME) ∣) ,
--     trunc-rec (isprop (q <ᵣ (0 % 1))) (λ { (r , (α , β)) → ASSUME })
--   )
--   ( λ q →
--     (λ uq → ∣ (q *ᵣ (1 % 2)) , (ASSUME , ASSUME) ∣) ,
--     trunc-rec (isprop ((0 % 1) <ᵣ q)) λ { (r , (α , β)) → ASSUME }
--   )
--   -- Disjoint
--   (λ { q (α , β) → ASSUME })
--   -- Located
--   (λ x y z → ASSUME)


_+r_ : ℝ → ℝ → ℝ
a +r b = record
  { lower = λ q → ∃ ℚ λ r → ∃ ℚ λ s → (lower a r ∧ lower b s) ∧ ((r +ᵣ s) ==ᵣ q)
  ; upper = λ q → ∃ ℚ λ r → ∃ ℚ λ s → (upper a r ∧ upper b s) ∧ ((r +ᵣ s) ==ᵣ q)
  ; lhabit = trunc-rec {P = {!!}} {!!} {!!} {!!}
  ; uhabit = {!!}
  ; lround = {!!}
  ; uround = {!!}
  ; disjoint = {!!}
  ; located = {!!}
  }
  where
    
