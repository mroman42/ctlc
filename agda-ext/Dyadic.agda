{-# OPTIONS --rewriting #-}

open import Base hiding (_+_)
open import Equality
open import naturals.Naturals
open import integers.Integers 
open import Prop

module Dyadic where

  record Dyadic : Set where
    constructor dyadic
    field
      mnt : ℤ
      exp : ℕ
      norm : normalized mnt exp
  open Dyadic public

  -- Normalization
  _*2^_ : ℤ → ℕ → Dyadic
  _*2^_ mnt zeroⁿ = dyadic mnt zeroⁿ **
  _*2^_ mnt (succⁿ exp) with (iseven-dec mnt)
  _*2^_ mnt (succⁿ exp) | inr x = dyadic mnt (succⁿ exp) x
  _*2^_ mnt (succⁿ exp) | inl x = (div2ᶻ mnt x) *2^ exp

  -- Normalization properties
  normd : (m : ℤ) → (e : ℕ) → (n : normalized m e) → m *2^ e ≡ dyadic m e n
  normd zeroᶻ zeroⁿ ** = refl
  normd zeroᶻ (succⁿ e) n = exfalso (n **)
  normd (pos zeroⁿ) zeroⁿ ** = refl
  normd (pos zeroⁿ) (succⁿ e) n = ap (dyadic (pos zeroⁿ) (succⁿ e)) (funext (λ ()))
  normd (pos (succⁿ x)) zeroⁿ ** = refl
  normd (pos (succⁿ x)) (succⁿ e) n with (iseven-dec (pos (succⁿ x)))
  normd (pos (succⁿ x)) (succⁿ e) n | inl p = exfalso (n p)
  normd (pos (succⁿ x)) (succⁿ e) n | inr p = ap (dyadic (pos (succⁿ x)) (succⁿ e) ) (funext λ u → exfalso (p u))
  normd (neg zeroⁿ) zeroⁿ ** = refl
  normd (neg zeroⁿ) (succⁿ e) n = ap (dyadic (neg zeroⁿ) (succⁿ e) ) (funext (λ ()))
  normd (neg (succⁿ x)) zeroⁿ ** = refl
  normd (neg (succⁿ x)) (succⁿ e) n with (iseven-dec (neg (succⁿ x)))
  normd (neg (succⁿ x)) (succⁿ e) n | inl p = exfalso (n p)
  normd (neg (succⁿ x)) (succⁿ e) n | inr p = ap (dyadic (neg (succⁿ x)) (succⁿ e) ) (funext λ u → exfalso (p u))

  n-zero : (e : ℕ) → zeroᶻ *2^ e ≡ zeroᶻ *2^ zeroⁿ
  n-zero zeroⁿ = refl
  n-zero (succⁿ e) = n-zero e
  {-# REWRITE n-zero #-}


  -- Operations on dyadics
  div2 : Dyadic → Dyadic
  div2 (dyadic m e n) with (iseven-dec m)
  div2 (dyadic m e n) | inl x = {!!}
  div2 (dyadic m e n) | inr x = {!!}

  zero : Dyadic
  zero = dyadic zeroᶻ zeroⁿ **

  one : Dyadic
  one = dyadic (pos zeroⁿ) zeroⁿ **

  1/2 : Dyadic
  1/2 = dyadic (pos zeroⁿ) 1 (λ z → z)

  -- Negation
  -_ : Dyadic → Dyadic
  - (dyadic m e n) = (-ᶻ m) *2^ e

  -- Addition
  _+_ : Dyadic → Dyadic → Dyadic
  dyadic m zeroⁿ n + dyadic m' e' n' = dyadic ((exp2 e') *ᶻ m +ᶻ m') zeroⁿ **
  dyadic m (succⁿ e) n + dyadic m' zeroⁿ n' = {!!}
  dyadic m (succⁿ e) n + dyadic m' (succⁿ e') n' = {!!}

  -- +ᵈ-lzero : (d : Dyadic) → zero + d ≡ d
  -- +ᵈ-lzero (dyadic m n e) = normd m n e

  -- +ᵈ-rzeroⁿ : (d : Dyadic) → d + zero ≡ d
  -- +ᵈ-rzeroⁿ (dyadic m e n) = normd m e n

  -- Multiplication
  _*_ : Dyadic → Dyadic → Dyadic
  dyadic m e n * dyadic m' e' n' = (m *ᶻ m') *2^ (e +ⁿ e')

  *lzero : (d : Dyadic) → zero * d ≡ zero
  *lzero (dyadic m zeroⁿ n) = refl
  *lzero (dyadic m (succⁿ e) n) = refl

  *rzero : (d : Dyadic) → d * zero ≡ zero
  *rzero (dyadic m e n) = refl

  -- Ordering
  _<ᵈ_ : Dyadic → Dyadic → Prop
  dyadic m e n <ᵈ dyadic m' e' n' = (m *ᶻ exp2 e' <ᶻ m' *ᶻ exp2 e)

  <ᵈ-*pos : {a c d : Dyadic} → Prf ((zero <ᵈ a) ~> (c <ᵈ d) ~> ((a * c) <ᵈ (a * d)))
  <ᵈ-*pos {dyadic a f o} {dyadic m e n} {dyadic m' e' n'} p q = {!!}

  
