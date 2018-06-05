{-# OPTIONS --without-K #-}


-- Agda-hott library.
-- Author: Mario Román

-- Naturals.  A basic implementation of the natural numbers and some
-- lemmas on them using the inductive definition.

open import Agda.Primitive
open import Base
open import Equality
open import logic.Sets
open import logic.Hedberg
open import logic.Propositions
open import equality.Sigma
open import equality.DecidableEquality
open import algebra.Monoids

module numbers.Naturals where

  -- Addition of natural numbers
  plus : ℕ → ℕ → ℕ
  plus zero y = y
  plus (succ x) y = succ (plus x y)

  infixl 60 _+ₙ_
  _+ₙ_ : ℕ → ℕ → ℕ
  _+ₙ_ = plus

  -- Lemmas about addition
  plus-lunit : (n : ℕ) → zero +ₙ n == n
  plus-lunit n = refl n

  plus-runit : (n : ℕ) → n +ₙ zero == n
  plus-runit zero = refl zero
  plus-runit (succ n) = ap succ (plus-runit n)

  plus-succ : (n m : ℕ) → succ (n +ₙ m) == (n +ₙ (succ m))
  plus-succ zero     m = refl (succ m)
  plus-succ (succ n) m = ap succ (plus-succ n m)

  plus-succ-rs : (n m o p : ℕ) → n +ₙ m == o +ₙ p → n +ₙ (succ m) == o +ₙ (succ p)
  plus-succ-rs n m o p α = inv (plus-succ n m) · ap succ α · (plus-succ o p)

  -- Commutativity
  plus-comm : (n m : ℕ) → n +ₙ m == m +ₙ n
  plus-comm zero     m = inv (plus-runit m)
  plus-comm (succ n) m = ap succ (plus-comm n m) · plus-succ m n

  -- Associativity
  plus-assoc : (n m p : ℕ) → n +ₙ (m +ₙ p) == (n +ₙ m) +ₙ p
  plus-assoc zero     m p = refl (m +ₙ p)
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

  -- The successor function is injective
  succ-inj : {n m : ℕ} → (succ n == succ m) → n == m
  succ-inj {n} {m} p = decode n m (encode (succ n) (succ m) p)

  +-inj : (k : ℕ) {n m : ℕ} → (k +ₙ n == k +ₙ m) → n == m
  +-inj zero   p = p
  +-inj (succ k) p = +-inj k (succ-inj p)
  
  nat-decEq : decEq ℕ
  nat-decEq zero zero = inl (refl zero)
  nat-decEq zero (succ m) = inr (λ ())
  nat-decEq (succ n) zero = inr (λ ())
  nat-decEq (succ n) (succ m) with (nat-decEq n m)
  nat-decEq (succ n) (succ m) | inl p = inl (ap succ p)
  nat-decEq (succ n) (succ m) | inr f = inr λ p → f (succ-inj p)

  nat-isSet : isSet ℕ
  nat-isSet = hedberg nat-decEq

  -- Naturals form a monoid with addition
  ℕ-plus-monoid : Monoid
  ℕ-plus-monoid = record
    { G = ℕ
    ; GisSet = nat-isSet
    ; _<>_ = plus
    ; e = zero
    ; lunit = plus-lunit
    ; runit = plus-runit
    ; assoc = plus-assoc
    }

  -- Ordering
  _<ₙ_ : ℕ → ℕ → Type0
  n <ₙ m = Σ ℕ (λ k → n +ₙ succ k == m)

  <-isProp : (n m : ℕ) → isProp (n <ₙ m)
  <-isProp n m (k1 , p1) (k2 , p2) = Σ-bycomponents (succ-inj (+-inj n (p1 · inv p2)) , nat-isSet _ _ _ _)

  
