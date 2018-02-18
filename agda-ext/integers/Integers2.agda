{-# OPTIONS --rewriting #-}

open import Base hiding (_+_)
open import Equality

module Integers2 where

  data ℤ : Set where
    zero : ℤ
    succ : ℤ → ℤ
    pred : ℤ → ℤ

  postulate succpred : ∀ a → succ (pred a) ≡ a
  postulate predsucc : ∀ a → pred (succ a) ≡ a
  {-# REWRITE succpred #-}
  {-# REWRITE predsucc #-}

  
  infixl 60 _+_
  _+_ : ℤ → ℤ → ℤ
  zero + b = b
  succ a + b = succ (a + b)
  pred a + b = pred (a + b)

  +rzero : ∀ n → n + zero ≡ n
  +rzero zero = refl
  +rzero (succ n) = ap succ (+rzero n)
  +rzero (pred n) = ap pred (+rzero n)
  {-# REWRITE +rzero #-}

  -- Pero no sabemos si una función dada está bien definida!
