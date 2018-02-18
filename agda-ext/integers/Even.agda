{-# OPTIONS --rewriting #-}

open import Base renaming (_+_ to _+ₒ_)
open import Prop
open import Equality
open import naturals.Naturals
open import integers.Definition
open import integers.Successor
open import integers.Addition
open import integers.Multiplication


module integers.Even where

  -- Even numbers
  iseven : ℤ → Set
  iseven zero = ⊤
  iseven (pos zeroⁿ) = ⊥
  iseven (pos (succⁿ zeroⁿ)) = ⊤
  iseven (pos (succⁿ (succⁿ x))) = iseven (pos x)
  iseven (neg zeroⁿ) = ⊥
  iseven (neg (succⁿ zeroⁿ)) = ⊤
  iseven (neg (succⁿ (succⁿ x))) = iseven (neg x)

  iseven-dec : ∀ z → (iseven z) +ₒ ¬ (iseven z)
  iseven-dec zero = inl **
  iseven-dec (pos zeroⁿ) = inr (λ ())
  iseven-dec (pos (succⁿ zeroⁿ)) = inl **
  iseven-dec (pos (succⁿ (succⁿ x))) = iseven-dec (pos x)
  iseven-dec (neg zeroⁿ) = inr (λ ())
  iseven-dec (neg (succⁿ zeroⁿ)) = inl **
  iseven-dec (neg (succⁿ (succⁿ x))) = iseven-dec (neg x)

  div2 : ∀ z → (iseven z) → ℤ
  div2 zero evenz = zero
  div2 (pos zeroⁿ) ()
  div2 (pos (succⁿ zeroⁿ)) evenz = pos zeroⁿ
  div2 (pos (succⁿ (succⁿ x))) evenz = succ (div2 (pos x) evenz)
  div2 (neg zeroⁿ) ()
  div2 (neg (succⁿ zeroⁿ)) evenz = neg zeroⁿ
  div2 (neg (succⁿ (succⁿ x))) evenz = pred (div2 (neg x) evenz)

  exp2 : ℕ → ℤ
  exp2 zeroⁿ = pos zeroⁿ
  exp2 (succⁿ n) = pos (succⁿ zeroⁿ) * exp2 n


  normalized : ℤ → ℕ → Set
  normalized mnt zeroⁿ = ⊤
  normalized mnt (succⁿ exp) = ¬ (iseven mnt)

  normalized-dec : (z : ℤ) → (n : ℕ) → (normalized z n) +ₒ ¬ (normalized z n)
  normalized-dec z zeroⁿ = inl **
  normalized-dec z (succⁿ n) with (iseven-dec z)
  normalized-dec z (succⁿ n) | inl x = inr (λ f → f x)
  normalized-dec z (succⁿ n) | inr x = inl x
