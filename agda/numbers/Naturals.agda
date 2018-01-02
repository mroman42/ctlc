{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality

module numbers.Naturals where


  -- TODO: Naturals are a set

  -- Addition of natural numbers
  plus : ℕ → ℕ → ℕ
  plus zero y = y
  plus (succ x) y = succ (plus x y)

  -- Lemmas about addition
  plus-lunit : (n : ℕ) → plus zero n == n
  plus-lunit n = refl n

  plus-runit : (n : ℕ) → plus n zero == n
  plus-runit zero = refl zero
  plus-runit (succ n) = ap succ (plus-runit n)


  -- Associativity
  plus-assoc : (n m p : ℕ) → plus n (plus m p) == plus (plus n m) p
  plus-assoc zero m p = refl (plus m p)
  plus-assoc (succ n) m p = ap succ (plus-assoc n m p)
