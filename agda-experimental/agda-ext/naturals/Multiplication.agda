{-# OPTIONS --rewriting #-}

open import Equality
open import naturals.Definition
open import naturals.Addition

module naturals.Multiplication where

  -- Definition
  _*_ : ℕ → ℕ → ℕ
  zero * m = zero
  succ n * m = (n * m) + m

  *rzero : ∀ n → n * zero ≡ zero
  *rzero zero = refl
  *rzero (succ n) = *rzero n
  {-# REWRITE *rzero #-}

  *runit : ∀ n → n * 1 ≡ n
  *runit zero = refl
  *runit (succ n) = ap succ (*runit n)
  {-# REWRITE *runit #-}  

  *rsucc : ∀ n m → n * succ m ≡ (n * m) + n
  *rsucc zero m = refl
  *rsucc (succ n) m = ap succ ((ap (_+ m) (*rsucc n m)) · ap ((n * m) +_) (+comm n m))
  {-# REWRITE *rsucc #-}

  *comm : ∀ n m → n * m ≡ m * n
  *comm zero m = refl
  *comm (succ n) m = ap (_+ m) (*comm n m)
