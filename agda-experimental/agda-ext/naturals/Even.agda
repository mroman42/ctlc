{-# OPTIONS --rewriting #-}

open import Base hiding (_+_)
open import Prop
open import Bool
open import Equality
open import naturals.Definition
open import naturals.Successor
open import naturals.Addition
open import naturals.Ordering
open import naturals.Multiplication

module naturals.Even where

  even : ℕ → Bool
  even zero = tt
  even (succ zero) = ff
  even (succ (succ n)) = even n

  Even : ℕ → Prop
  Even z = even z ≡≡ tt

  even-succ : ∀ n → even (succ n) ≡ ~ (even n)
  even-succ zero = refl
  even-succ (succ n) = inv (ap ~ (even-succ n))
  {-# REWRITE even-succ #-}

  even-plus : ∀ n m → even (n + m) ≡ even n +ᵇ even m
  even-plus zero m = refl
  even-plus (succ n) m = ap ~ (even-plus n m)
  {-# REWRITE even-plus #-}

  even-mult : ∀ n m → even (n * m) ≡ even n *ᵇ even m
  even-mult zero m = refl
  even-mult (succ zero) m = refl
  even-mult (succ (succ n)) m = even-mult n m
  {-# REWRITE even-mult #-}


  exp2n : ℕ → ℕ
  exp2n zero = 1
  exp2n (succ n) = 2 * (exp2n n)

  exp2-1 : ℕ → ℕ
  exp2-1 zero = zero
  exp2-1 (succ n) = exp2n n + exp2-1 n

  exp2succ : ∀ n → succ (exp2-1 n) ≡ exp2n n
  exp2succ zero = refl
  exp2succ (succ n) = ap (exp2n n +_) (exp2succ n)
