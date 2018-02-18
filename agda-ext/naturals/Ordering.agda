{-# OPTIONS --rewriting #-}

open import Base hiding (_+_)
open import Prop
open import naturals.Definition
open import naturals.Addition

module naturals.Ordering where

  -- Ordering
  _<_ : ℕ → ℕ → Prop
  m < zero = ⊥ₚ
  zero < succ m = ⊤ₚ
  succ n < succ m = n < m

  _≥ⁿ_ : (n m : ℕ) → Prop
  n ≥ⁿ m = Not (n < m)

  ≥zero : ∀ n → Prf (n ≥ⁿ 0)
  ≥zero zero p = p
  ≥zero (succ n) p = p
  
  <plus : ∀ k n m → Prf ((n < m) ~> ((k + n) < (k + m)))
  <plus zero n m p = p
  <plus (succ k) n m p = <plus k n m p

  <trans : ∀ n m k → Prf ((n < m) ~> (m < k) ~> (n < k))
  <trans zero zero k p q = q
  <trans zero (succ m) zero p q = q
  <trans zero (succ m) (succ k) p q = **
  <trans (succ n) zero zero p q = q
  <trans (succ n) zero (succ k) () q
  <trans (succ n) (succ m) zero p q = q
  <trans (succ n) (succ m) (succ k) p q = <trans n m k p q
