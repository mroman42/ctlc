{-# OPTIONS --rewriting #-}

open import Prop
open import Equality
open import naturals.Naturals
open import integers.Definition

module integers.Successor where

  succ : ℤ → ℤ
  succ (pos n) = pos (succⁿ n)
  succ (negm1 0) = pos 0
  succ (negm1 (succⁿ n)) = negm1 n
  
  pred : ℤ → ℤ
  pred (pos 0) = negm1 0
  pred (pos (succⁿ x)) = pos x
  pred (negm1 x) = negm1 (succⁿ x)

  succpred-id : ∀ n → succ (pred n) ≡ n
  succpred-id (pos 0) = refl
  succpred-id (pos (succⁿ x)) = refl
  succpred-id (negm1 x) = refl
  {-# REWRITE succpred-id #-}

  predsucc-id : ∀ n → pred (succ n) ≡ n
  predsucc-id (pos x) = refl
  predsucc-id (negm1 zeroⁿ) = refl
  predsucc-id (negm1 (succⁿ x)) = refl
  {-# REWRITE predsucc-id #-}

  -- Successor injective
  succ-inj-l : ∀ n m → (n ≡ m) → (succ n ≡ succ m)
  succ-inj-l n m p = ap succ p
  
  -- succ-inj-r : ∀ n m → (succ n ≡ succ m) -> (n ≡ m)
  -- succ-inj-r zero zero p = refl
  -- succ-inj-r zero (pos x) ()
  -- succ-inj-r zero (neg zeroⁿ) ()
  -- succ-inj-r zero (neg (succⁿ x)) ()
  -- succ-inj-r (pos x) zero ()
  -- succ-inj-r (pos zeroⁿ) (pos zeroⁿ) p = refl
  -- succ-inj-r (pos zeroⁿ) (pos (succⁿ m)) ()
  -- succ-inj-r (pos (succⁿ x)) (pos zeroⁿ) ()
  -- succ-inj-r (pos (succⁿ x)) (pos (succⁿ .x)) refl = refl
  -- succ-inj-r (pos x) (neg zeroⁿ) ()
  -- succ-inj-r (pos x) (neg (succⁿ m)) ()
  -- succ-inj-r (neg zeroⁿ) zero ()
  -- succ-inj-r (neg zeroⁿ) (pos x) ()
  -- succ-inj-r (neg zeroⁿ) (neg zeroⁿ) p = refl
  -- succ-inj-r (neg zeroⁿ) (neg (succⁿ x)) ()
  -- succ-inj-r (neg (succⁿ x)) zero ()
  -- succ-inj-r (neg (succⁿ x)) (pos m) ()
  -- succ-inj-r (neg (succⁿ x)) (neg zeroⁿ) ()
  -- succ-inj-r (neg (succⁿ x)) (neg (succⁿ .x)) refl = refl
