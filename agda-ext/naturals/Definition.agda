{-# OPTIONS --rewriting #-}

module naturals.Definition where

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}  
