{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality
open import logic.Sets
open import logic.Hedberg
open import equality.DecidableEquality
open import algebra.Monoids

module numbers.Integers2 where

  data ℤ : Type0 where
    zer : ℤ
    pos : ℕ → ℤ
    neg : ℕ → ℤ

  -- Successor function
  zsucc : ℤ → ℤ
  zsucc zer            = pos 0
  zsucc (pos x)        = pos (succ x)
  zsucc (neg zero)     = zer
  zsucc (neg (succ x)) = neg x

  -- Predecessor function
  zpred : ℤ → ℤ
  zpred zer            = neg 0
  zpred (pos zero)     = zer
  zpred (pos (succ x)) = pos x
  zpred (neg x)        = neg (succ x)

  -- Successor and predecessors
  succ-pred-id : (n : ℤ) → zsucc (zpred n) == n
  succ-pred-id = {!!}
