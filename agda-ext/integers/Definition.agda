{-# OPTIONS --rewriting #-}

open import naturals.Naturals

module integers.Definition where

  data ℤ : Set where
    zero : ℤ
    pos : ℕ → ℤ
    neg : ℕ → ℤ

  NtoZ : ℕ → ℤ
  NtoZ zeroⁿ = zero
  NtoZ (succⁿ n) = pos n
