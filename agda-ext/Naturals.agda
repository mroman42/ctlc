{-# OPTIONS --rewriting #-}

open import Equality
open import Base
open import Prop

module Naturals where

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}

  -- Definition of addition
  _+ⁿ_ : ℕ → ℕ → ℕ
  0      +ⁿ m = m
  succ n +ⁿ m = succ (n +ⁿ m)

  
  +ⁿ-rzero : (n : ℕ) → n +ⁿ 0 ≡ n
  +ⁿ-rzero 0 = refl
  +ⁿ-rzero (succ n) = ap succ (+ⁿ-rzero n)
  {-# REWRITE +ⁿ-rzero #-}

  +ⁿ-rsucc : (n m : ℕ) → n +ⁿ succ m ≡ succ n +ⁿ m
  +ⁿ-rsucc zero m = refl
  +ⁿ-rsucc (succ n) m = ap succ (+ⁿ-rsucc n m)
  {-# REWRITE +ⁿ-rsucc #-}

  +ⁿ-comm : (n m : ℕ) → n +ⁿ m ≡ m +ⁿ n
  +ⁿ-comm zero m = refl
  +ⁿ-comm (succ n) m = ap succ (+ⁿ-comm n m)

  +ⁿ-assoc : (n m o : ℕ) → n +ⁿ (m +ⁿ o) ≡ (n +ⁿ m) +ⁿ o
  +ⁿ-assoc zero m o = refl
  +ⁿ-assoc (succ n) m o = ap succ (+ⁿ-assoc n m o)
  {-# REWRITE +ⁿ-assoc #-}


  -- Successor injective
  succ-inj-l : ∀ n m → Prf ((n ≡≡ m) ~> (succ n ≡≡ succ m))
  succ-inj-l n m = {!!}

  -- Ordering
  _<ⁿ_ : (n m : ℕ) → Prop
  n <ⁿ m = ∃ ℕ (λ k → n +ⁿ succ k ≡≡ m)

  _≥ⁿ_ : (n m : ℕ) → Prop
  n ≥ⁿ m = Not (n <ⁿ m)

  ≥ⁿ-zero : ∀ n → Prf (n ≥ⁿ 0)
  ≥ⁿ-zero n p = trec
    {P = ⊥ₚ}
    (λ { (k , ()) }) p

  <ⁿ-succ-l : ∀ n m → Prf ((n <ⁿ m) ~> (succ n <ⁿ succ m))
  <ⁿ-succ-l n m p = trec
    {P = (succ n <ⁿ succ m)}
    (λ { (k , q) → ∣ k , ap succ q ∣ }) p

  <ⁿ-succ-r : ∀ n m → Prf ((succ n <ⁿ succ m) ~> (n <ⁿ m))
  <ⁿ-succ-r n m p = trec
    {P = n <ⁿ m}
    (λ { (k , q) → ∣ k , {!!} ∣ }) p

  <ⁿ-plus : ∀ k n m → Prf ((n <ⁿ m) ~> ((k +ⁿ n) <ⁿ (k +ⁿ m)))
  <ⁿ-plus k n m p = trec
    {P = (k +ⁿ n) <ⁿ (k +ⁿ m)}
    (λ { (o , q) → ∣ o , ap (k +ⁿ_) q ∣ }) p

  <ⁿ-zerosucc : ∀ n → Prf (0 <ⁿ succ n)
  <ⁿ-zerosucc n = ∣ n , refl ∣
  
  <ⁿ-trans : ∀ n m k → Prf ((n <ⁿ m) ~> (m <ⁿ k) ~> (n <ⁿ k))
  <ⁿ-trans n m k p q = trec {P = (n <ⁿ k)}
    (λ { (o , refl) → trec {P = (n <ⁿ k)}
      (λ { (u , refl) → ∣ succ (u +ⁿ o) , refl ∣ }) p }) q
