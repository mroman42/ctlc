module Reals where

open import Prop
open import Prelude.Bool
open import Prelude.Nat
open import Prelude.Equality
open import Prelude.Sum
open import Prelude.Product

record Fraction : Set where
  constructor frak
  field
    num+ : Nat
    num- : Nat
    densuc : Nat
open Fraction public


eqFrak : Fraction → Fraction → Bool
eqFrak (frak a b c) (frak a' b' c') = eqNat
  ((suc c') *N a +N (suc c) *N b')
  ((suc c) *N a +N (suc c') *N b)

lessFrak : Fraction → Fraction → Bool
lessFrak (frak a b c) (frak a' b' c') = lessNat
  ((suc c') *N a +N (suc c) *N b')
  ((suc c) *N a +N (suc c') *N b)

_≡ᶠ_ : Fraction → Fraction → Set
(frak a b c) ≡ᶠ (frak a' b' c') = 
  ((suc c') *N a +N (suc c) *N b') ≡
  ((suc c) *N a +N (suc c') *N b)



record ℝ : Set where
  field
    -- Dedekind cuts are
    lower : Fraction → Prop
    upper : Fraction → Prop

    -- Welldefined
    wlower : (a b : Fraction) → a ≡ᶠ b → Prf (lower a <~> lower b)
    wupper : (a b : Fraction) → a ≡ᶠ b → Prf (upper a <~> upper b)

    -- Inhabited
    lhabit : Prf (∃ Fraction lower)
    uhabit : Prf (∃ Fraction upper)

    -- Rounded
    lround : Prf (Forall Fraction (λ q → lower q <~> ∃ Fraction (λ r → (lessFrak q r ≡≡ true) ∧ lower r)))
    uround : Prf (Forall Fraction (λ q → upper q <~> ∃ Fraction (λ r → (lessFrak r q ≡≡ true) ∧ upper r)))

    -- Disjoint
    disjoint : Prf (Forall Fraction (λ q → Not (lower q ∧ upper q)))

    -- Located
    located : Prf (Forall Fraction (λ q → Forall Fraction (λ r → (lessFrak q r ≡≡ true) ~> (lower q ∨ upper r))))
open ℝ public


Rzero : ℝ
Rzero = record
          { lower = λ q → lessFrak q (frak 0 0 0) ≡≡ true
          ; upper = λ q → lessFrak (frak 0 0 0) q ≡≡ true
          ; wlower = λ a b x → (λ p → {!!}) , {!!}
          ; wupper = {!!}
          ; lhabit = {!!}
          ; uhabit = {!!}
          ; lround = {!!}
          ; uround = {!!}
          ; disjoint = {!!}
          ; located = {!!}
          }
