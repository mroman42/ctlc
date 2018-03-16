{-# OPTIONS --rewriting #-}

open import naturals.Naturals

module integers.Definition where

  data ℤ : Set where
    pos : ℕ → ℤ
    negm1 : ℕ → ℤ
