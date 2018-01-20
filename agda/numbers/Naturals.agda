{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality

module numbers.Naturals where

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


  -- Decidable equality
  -- Encode-decode technique for natural numbers
  code : ℕ → ℕ → Type0
  code 0        0        = ⊤
  code 0        (succ m) = ⊥
  code (succ n) 0        = ⊥
  code (succ n) (succ m) = code n m

  crefl : (n : ℕ) → code n n
  crefl zero     = ★
  crefl (succ n) = crefl n

  encode : (n m : ℕ) → (n == m) → code n m
  encode n m p = transport (code n) p (crefl n)

  decode : (n m : ℕ) → code n m → n == m
  decode zero zero c = refl zero
  decode zero (succ m) ()
  decode (succ n) zero ()
  decode (succ n) (succ m) c = ap succ (decode n m c)

  zero-not-succ : (n : ℕ) → ¬ (succ n == zero)
  zero-not-succ n = encode (succ n) 0

  succ-inj : (n m : ℕ) → (succ n == succ m) → n == m
  succ-inj n m p = decode n m (encode (succ n) (succ m) p)
  
  nat-decEq : (n m : ℕ) → (n == m) + ¬ (n == m)
  nat-decEq zero zero = inl (refl zero)
  nat-decEq zero (succ m) = inr (λ ())
  nat-decEq (succ n) zero = inr (λ ())
  nat-decEq (succ n) (succ m) with (nat-decEq n m)
  nat-decEq (succ n) (succ m) | inl p = inl (ap succ p)
  nat-decEq (succ n) (succ m) | inr f = inr λ p → f (succ-inj n m p)
