{-# OPTIONS --rewriting #-}

open import Prop
open import Equality
open import naturals.Naturals
open import integers.Definition

module integers.Successor where

  -- Successor and predecessor
  succ : ℤ → ℤ
  succ zero = pos 0
  succ (pos x) = pos (succⁿ x)
  succ (neg zeroⁿ) = zero
  succ (neg (succⁿ x)) = neg x

  pred : ℤ → ℤ
  pred zero = neg 0
  pred (pos zeroⁿ) = zero
  pred (pos (succⁿ x)) = pos x
  pred (neg x) = neg (succⁿ x)

  succpred-id : ∀ n → succ (pred n) ≡ n
  succpred-id zero = refl
  succpred-id (pos zeroⁿ) = refl
  succpred-id (pos (succⁿ n)) = refl
  succpred-id (neg n) = refl
  {-# REWRITE succpred-id #-}

  predsucc-id : ∀ n → pred (succ n) ≡ n
  predsucc-id zero            = refl
  predsucc-id (pos n)        = refl
  predsucc-id (neg zeroⁿ)     = refl
  predsucc-id (neg (succⁿ n)) = refl
  {-# REWRITE predsucc-id #-}

  -- Successor injective
  succ-inj-l : ∀ n m → (n ≡ m) -> (succ n ≡ succ m)
  succ-inj-l n m p = ap succ p
  
  succ-inj-r : ∀ n m → (succ n ≡ succ m) -> (n ≡ m)
  succ-inj-r zero zero p = refl
  succ-inj-r zero (pos x) ()
  succ-inj-r zero (neg zeroⁿ) ()
  succ-inj-r zero (neg (succⁿ x)) ()
  succ-inj-r (pos x) zero ()
  succ-inj-r (pos zeroⁿ) (pos zeroⁿ) p = refl
  succ-inj-r (pos zeroⁿ) (pos (succⁿ m)) ()
  succ-inj-r (pos (succⁿ x)) (pos zeroⁿ) ()
  succ-inj-r (pos (succⁿ x)) (pos (succⁿ .x)) refl = refl
  succ-inj-r (pos x) (neg zeroⁿ) ()
  succ-inj-r (pos x) (neg (succⁿ m)) ()
  succ-inj-r (neg zeroⁿ) zero ()
  succ-inj-r (neg zeroⁿ) (pos x) ()
  succ-inj-r (neg zeroⁿ) (neg zeroⁿ) p = refl
  succ-inj-r (neg zeroⁿ) (neg (succⁿ x)) ()
  succ-inj-r (neg (succⁿ x)) zero ()
  succ-inj-r (neg (succⁿ x)) (pos m) ()
  succ-inj-r (neg (succⁿ x)) (neg zeroⁿ) ()
  succ-inj-r (neg (succⁿ x)) (neg (succⁿ .x)) refl = refl
