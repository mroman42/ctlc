{-# OPTIONS --rewriting #-}

open import Base
open import Equality
open import Naturals
open import Integers
open import Prop

module Dyadic where

  iseven : ℤ → Set
  iseven zer = ⊤
  iseven (pos zero) = ⊥
  iseven (pos (succ zero)) = ⊤
  iseven (pos (succ (succ x))) = iseven (pos x)
  iseven (neg zero) = ⊥
  iseven (neg (succ zero)) = ⊤
  iseven (neg (succ (succ x))) = iseven (neg x)

  iseven-dec : (z : ℤ) → (iseven z) + ¬ (iseven z)
  iseven-dec zer = inl **
  iseven-dec (pos zero) = inr (λ ())
  iseven-dec (pos (succ zero)) = inl **
  iseven-dec (pos (succ (succ x))) = iseven-dec (pos x)
  iseven-dec (neg zero) = inr (λ ())
  iseven-dec (neg (succ zero)) = inl **
  iseven-dec (neg (succ (succ x))) = iseven-dec (neg x)

  div2 : (z : ℤ) → (iseven z) → ℤ
  div2 zer evenz = zer
  div2 (pos zero) ()
  div2 (pos (succ zero)) evenz = pos zero
  div2 (pos (succ (succ x))) evenz = zsucc (div2 (pos x) evenz)
  div2 (neg zero) ()
  div2 (neg (succ zero)) evenz = neg zero
  div2 (neg (succ (succ x))) evenz = zpred (div2 (neg x) evenz)

  exp2 : ℕ → ℤ
  exp2 zero = pos zero
  exp2 (succ n) = pos (succ zero) *ᶻ exp2 n

  normalized : ℤ → ℕ → Set
  normalized mnt zero = ⊤
  normalized mnt (succ exp) = ¬ (iseven mnt)

  record Dyadic : Set where
    constructor dyadic
    field
      mnt : ℤ
      exp : ℕ
      norm : normalized mnt exp
  open Dyadic public

  -- Normalization
  _*2^_ : ℤ → ℕ → Dyadic
  _*2^_ mnt zero = dyadic mnt zero **
  _*2^_ mnt (succ exp) with (iseven-dec mnt)
  _*2^_ mnt (succ exp) | inr x = dyadic mnt (succ exp) x
  _*2^_ mnt (succ exp) | inl x = (div2 mnt x) *2^ exp

  -- Normalization properties
  norm-d : (m : ℤ) → (e : ℕ) → (n : normalized m e) → m *2^ e ≡ dyadic m e n
  norm-d zer zero ** = refl
  norm-d zer (succ e) n = exfalso (n **)
  norm-d (pos zero) zero ** = refl
  norm-d (pos zero) (succ e) n = ap (dyadic (pos zero) (succ e)) (funext (λ ()))
  norm-d (pos (succ x)) zero ** = refl
  norm-d (pos (succ x)) (succ e) n with (iseven-dec (pos (succ x)))
  norm-d (pos (succ x)) (succ e) n | inl p = exfalso (n p)
  norm-d (pos (succ x)) (succ e) n | inr p = ap (dyadic (pos (succ x)) (succ e) ) (funext λ u → exfalso (p u))
  norm-d (neg zero) zero ** = refl
  norm-d (neg zero) (succ e) n = ap (dyadic (neg zero) (succ e) ) (funext (λ ()))
  norm-d (neg (succ x)) zero ** = refl
  norm-d (neg (succ x)) (succ e) n with (iseven-dec (neg (succ x)))
  norm-d (neg (succ x)) (succ e) n | inl p = exfalso (n p)
  norm-d (neg (succ x)) (succ e) n | inr p = ap (dyadic (neg (succ x)) (succ e) ) (funext λ u → exfalso (p u))

  norm-exp : (e : ℕ) → zer *2^ e ≡ zer *2^ zero
  norm-exp zero = refl
  norm-exp (succ e) = norm-exp e
  {-# REWRITE norm-exp #-}


  -- Operations on dyadics
  zeroᵈ : Dyadic
  zeroᵈ = dyadic zer zero **

  oneᵈ : Dyadic
  oneᵈ = dyadic (pos zero) zero **

  1/2ᵈ : Dyadic
  1/2ᵈ = dyadic (pos zero) 1 (λ z → z)

  -- Negation
  -ᵈ_ : Dyadic → Dyadic
  -ᵈ (dyadic m e n) = (- m) *2^ e

  -- Addition
  _+ᵈ_ : Dyadic → Dyadic → Dyadic
  dyadic m e n +ᵈ dyadic m' e' n' = (m *ᶻ exp2 e' +ᶻ exp2 e *ᶻ m') *2^ (e +ⁿ e')

  +ᵈ-lzero : (d : Dyadic) → zeroᵈ +ᵈ d ≡ d
  +ᵈ-lzero (dyadic m n e) = norm-d m n e

  +ᵈ-rzero : (d : Dyadic) → d +ᵈ zeroᵈ ≡ d
  +ᵈ-rzero (dyadic m e n) = norm-d m e n

  -- Multiplication
  _*ᵈ_ : Dyadic → Dyadic → Dyadic
  dyadic m e n *ᵈ dyadic m' e' n' = (m *ᶻ m') *2^ (e +ⁿ e')

  *ᵈ-lzero : (d : Dyadic) → zeroᵈ *ᵈ d ≡ zeroᵈ
  *ᵈ-lzero (dyadic m zero n) = refl
  *ᵈ-lzero (dyadic m (succ e) n) = refl

  *ᵈ-rzero : (d : Dyadic) → d *ᵈ zeroᵈ ≡ zeroᵈ
  *ᵈ-rzero (dyadic m e n) = refl

  -- Ordering
  _<ᵈ_ : Dyadic → Dyadic → Prop
  dyadic m e n <ᵈ dyadic m' e' n' = (m *ᶻ exp2 e' <ᶻ m' *ᶻ exp2 e)

  <ᵈ-*pos : {a c d : Dyadic} → Prf ((zeroᵈ <ᵈ a) ~> (c <ᵈ d) ~> ((a *ᵈ c) <ᵈ (a *ᵈ d)))
  <ᵈ-*pos {dyadic a f o} {dyadic m e n} {dyadic m' e' n'} p q = {!!}

  
