{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality
open import logic.Sets
open import logic.Hedberg
open import equivalence.Equivalence
open import equivalence.Quasiinverses
open import equality.DecidableEquality
open import numbers.Naturals
open import algebra.Monoids

module numbers.Integers3 where

  data ℤ : Type0 where
    pos : ℕ → ℤ
    neg1 : ℕ → ℤ

  -- Successor and predecessor functions
  zsucc : ℤ → ℤ
  zsucc (pos x)         = pos (succ x)
  zsucc (neg1 zero)     = pos 0
  zsucc (neg1 (succ x)) = neg1 x

  zpred : ℤ → ℤ
  zpred (pos zero) = neg1 0
  zpred (pos (succ x)) = pos x
  zpred (neg1 x) = neg1 (succ x)

  -- Relation between successor and predecessor
  zsuccpred-id : (n : ℤ) → zsucc (zpred n) == n
  zsuccpred-id (pos zero) = refl _
  zsuccpred-id (pos (succ x)) = refl _
  zsuccpred-id (neg1 x) = refl _

  zpredsucc-id : (n : ℤ) → zpred (zsucc n) == n
  zpredsucc-id (pos x) = refl _
  zpredsucc-id (neg1 zero) = refl _
  zpredsucc-id (neg1 (succ x)) = refl _

  -- Equivalence given by successor and predecessor
  zequiv-succ : ℤ ≃ ℤ
  zequiv-succ = qinv-≃ zsucc (zpred , (zsuccpred-id , zpredsucc-id))

  _+ᶻ_ : ℤ → ℤ → ℤ
  pos n +ᶻ pos m  = pos (n +ₙ m)
  pos n +ᶻ neg1 m = {!!}
  neg1 n +ᶻ y     = {!!}
    where
      _-_ : ℕ → ℕ → ℤ
      n - zero = pos n
      zero - succ m = neg1 m
      succ n - succ m = n - m
