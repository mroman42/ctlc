{-# OPTIONS --rewriting #-}

module Fractions where

open import Naturals renaming
  ( _≡?_ to _≡?ⁿ_
  ; _+_ to _+ⁿ_
  ; _*_ to _*ⁿ_
  ; +comm to +commⁿ 
  )
  public

record Fraction : Set where
  constructor frak
  field
    n+ : ℕ
    n- : ℕ
    dsuc : ℕ
open Fraction public


infix 5 _≡?_
_≡?_ : Fraction → Fraction → Bool
(frak a b c) ≡? (frak a' b' c') =
  ((a *ⁿ (succ c')) +ⁿ (b' *ⁿ (succ c)) ≡?ⁿ (a' *ⁿ (succ c)) +ⁿ (b *ⁿ (succ c')))


_+_ : Fraction → Fraction → Fraction
frak a b c + frak a' b' c' = frak
  (a *ⁿ (succ c') +ⁿ a' *ⁿ (succ c))
  (b *ⁿ (succ c') +ⁿ b' *ⁿ (succ c))
  (c *ⁿ c' +ⁿ c +ⁿ c')


+comm : ∀ a b → (a + b ≡? b + a) ≡ true
+comm (frak a b c) (frak a' b' c') = {!!}
