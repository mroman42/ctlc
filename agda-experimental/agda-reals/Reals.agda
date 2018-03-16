open import Numeric.Rational
open import Prelude.Nat
open import Prelude.Int
open import Prelude.Sum
open import Prop

module Reals where

  record Real : Set where
    constructor real
    field
      lower : Rational → Prop
      upper : Rational → Prop

      -- Inhabited
      lhabit : Prf (∃ Rational lower)
      uhabit : Prf (∃ Rational upper)

      -- Rounded
      lround : Prf (Forall Rational (λ q → lower q <~> ∃ Rational (λ r → q < r ∧ lower r)))
      uround : Prf (Forall Rational (λ q → upper q <~> ∃ Rational (λ r → r < q ∧ upper r)))

      -- Disjoint
      disjoint : Prf (Forall Rational (λ q → Not (lower q ∧ upper q)))

      -- Located
      located : Prf (Forall Rational (λ q → Forall Rational (λ r → q < r ~> (lower q ∨ upper r))))
