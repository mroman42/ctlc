{-# OPTIONS --rewriting #-}

open import Equality
open import naturals.Naturals
open import integers.Definition
open import integers.Successor
open import integers.Addition

module integers.Multiplication where

  -- Multiplication
  infixl 70 _*_
  _*_ : ℤ → ℤ → ℤ
  zero * m = zero
  pos zeroⁿ * m = m
  pos (succⁿ x) * m = (pos x * m) + m
  neg zeroⁿ * m = - m
  neg (succⁿ x) * m = (neg x * m) + (- m)

  *-rzero : ∀ n → n * zero ≡ zero
  *-rzero zero = refl
  *-rzero (pos zeroⁿ) = refl
  *-rzero (pos (succⁿ x)) = *-rzero (pos x)
  *-rzero (neg zeroⁿ) = refl
  *-rzero (neg (succⁿ x)) = *-rzero (neg x)
  {-# REWRITE *-rzero #-}

  *-rone : ∀ n → n * pos zeroⁿ ≡ n
  *-rone zero = refl
  *-rone (pos zeroⁿ) = refl
  *-rone (pos (succⁿ x)) = ap succ (*-rone (pos x))
  *-rone (neg zeroⁿ) = refl
  *-rone (neg (succⁿ x)) = ap pred (*-rone (neg x))
  {-# REWRITE *-rone #-}

  *-rmone : ∀ n → n * neg zeroⁿ ≡ - n
  *-rmone zero = refl
  *-rmone (pos zeroⁿ) = refl
  *-rmone (pos (succⁿ x)) = ap pred (*-rmone (pos x))
  *-rmone (neg zeroⁿ) = refl
  *-rmone (neg (succⁿ x)) = ap succ (*-rmone (neg x))
  {-# REWRITE *-rmone #-}

  *-rpossucc : (n : ℕ) → (m : ℤ) → m * pos (succⁿ n) ≡ m + m * pos n
  *-rpossucc n zero = refl
  *-rpossucc n (pos zeroⁿ) = refl
  *-rpossucc n (pos (succⁿ x)) = ap (λ u → succ (u + pos n)) (*-rpossucc n (pos x))
  *-rpossucc n (neg zeroⁿ) = refl
  *-rpossucc n (neg (succⁿ x)) = ap (λ u → pred (u + neg n)) (*-rpossucc n (neg x))
  {-# REWRITE *-rpossucc #-}

  *-rnegsucc : (n : ℕ) → (m : ℤ) → m * neg (succⁿ n) ≡ (- m) + m * neg n
  *-rnegsucc n zero = refl
  *-rnegsucc n (pos zeroⁿ) = refl
  *-rnegsucc n (pos (succⁿ x)) = ap (λ u → pred (u + neg n)) (*-rnegsucc n (pos x))
  *-rnegsucc n (neg zeroⁿ) = refl
  *-rnegsucc n (neg (succⁿ x)) = ap (λ u → succ (u + pos n)) (*-rnegsucc n (neg x))
  {-# REWRITE *-rnegsucc #-}
  
