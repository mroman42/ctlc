{-# OPTIONS --without-K #-}


-- Agda-hott library.
-- Author: Mario Román

-- Integers.  Inductive representation of the integers. It defines
-- ordering and an equivalence given by the successor and predecessor
-- functions that will be used in the homotopical proof of the
-- fundamental group of the circle.

open import Base
open import Equality
open import logic.Sets
open import logic.Hedberg
open import EquationalReasoning
open import equivalence.Equivalence
open import equivalence.Quasiinverses
open import equality.DecidableEquality
open import numbers.Naturals
open import algebra.Monoids

module numbers.Integers where

  data ℤ : Type0 where
    zer : ℤ
    pos : ℕ → ℤ
    neg : ℕ → ℤ

  -- Inclusion of the natural numbers into the integers
  NtoZ : ℕ → ℤ
  NtoZ zero     = zer
  NtoZ (succ n) = pos n

  -- Successor function
  zsucc : ℤ → ℤ
  zsucc zer            = pos 0
  zsucc (pos x)        = pos (succ x)
  zsucc (neg zero)     = zer
  zsucc (neg (succ x)) = neg x

  -- Predecessor function
  zpred : ℤ → ℤ
  zpred zer            = neg 0
  zpred (pos zero)     = zer
  zpred (pos (succ x)) = pos x
  zpred (neg x)        = neg (succ x)

  -- Successor and predecessor
  zsuccpred-id : (n : ℤ) → zsucc (zpred n) == n
  zsuccpred-id zer            = refl _
  zsuccpred-id (pos zero)     = refl _
  zsuccpred-id (pos (succ n)) = refl _
  zsuccpred-id (neg n)        = refl _

  zpredsucc-id : (n : ℤ) → zpred (zsucc n) == n
  zpredsucc-id zer            = refl _
  zpredsucc-id (pos n)        = refl _
  zpredsucc-id (neg zero)     = refl _
  zpredsucc-id (neg (succ n)) = refl _

  zpredsucc-succpred : (n : ℤ) → zpred (zsucc n) == zsucc (zpred n)
  zpredsucc-succpred zer = refl zer
  zpredsucc-succpred (pos zero) = refl (pos zero)
  zpredsucc-succpred (pos (succ x)) = refl (pos (succ x))
  zpredsucc-succpred (neg zero) = refl (neg zero)
  zpredsucc-succpred (neg (succ x)) = refl (neg (succ x))

  zsuccpred-predsucc : (n : ℤ) → zsucc (zpred n) == zpred (zsucc n)
  zsuccpred-predsucc n = inv (zpredsucc-succpred n)
  
  -- Equivalence given by successor and predecessor
  zequiv-succ : ℤ ≃ ℤ
  zequiv-succ = qinv-≃ zsucc (zpred , (zsuccpred-id , zpredsucc-id))

  -- Negation
  - : ℤ → ℤ
  - zer     = zer
  - (pos x) = neg x
  - (neg x) = pos x

  double- : (z : ℤ) → - (- z) == z
  double- zer = refl _
  double- (pos x) = refl _
  double- (neg x) = refl _

  zequiv- : ℤ ≃ ℤ
  zequiv- = qinv-≃ - (- , (double- , double-))

  -- Addition on integers
  infixl 60 _+ᶻ_
  _+ᶻ_ : ℤ → ℤ → ℤ
  zer +ᶻ m = m
  pos zero +ᶻ m = zsucc m
  pos (succ x) +ᶻ m = zsucc (pos x +ᶻ m)
  neg zero +ᶻ m = zpred m
  neg (succ x) +ᶻ m = zpred (neg x +ᶻ m)

  -- Lemmas on addition
  +ᶻ-lunit : (n : ℤ) → n == n +ᶻ zer
  +ᶻ-lunit zer            = refl _
  +ᶻ-lunit (pos zero)     = refl _
  +ᶻ-lunit (pos (succ x)) = ap zsucc (+ᶻ-lunit (pos x))
  +ᶻ-lunit (neg zero)     = refl _
  +ᶻ-lunit (neg (succ x)) = ap zpred (+ᶻ-lunit (neg x))


  +ᶻ-unit-zsucc : (n : ℤ) → zsucc n == (n +ᶻ pos zero)
  +ᶻ-unit-zsucc zer = refl _
  +ᶻ-unit-zsucc (pos zero) = refl _
  +ᶻ-unit-zsucc (pos (succ x)) = ap zsucc (+ᶻ-unit-zsucc (pos x))
  +ᶻ-unit-zsucc (neg zero) = refl _
  +ᶻ-unit-zsucc (neg (succ x)) = inv (zpredsucc-id (neg x)) · ap zpred (+ᶻ-unit-zsucc (neg x))

  +ᶻ-unit-zpred : (n : ℤ) → zpred n == (n +ᶻ neg zero)
  +ᶻ-unit-zpred zer = refl _
  +ᶻ-unit-zpred (pos zero) = refl zer
  +ᶻ-unit-zpred (pos (succ x)) = inv (zsuccpred-id (pos x)) · ap zsucc (+ᶻ-unit-zpred (pos x))
  +ᶻ-unit-zpred (neg zero) = refl _
  +ᶻ-unit-zpred (neg (succ x)) = ap zpred (+ᶻ-unit-zpred (neg x))


  +ᶻ-pos-zsucc : (n : ℤ) → (x : ℕ) → zsucc (n +ᶻ pos x) == n +ᶻ pos (succ x)
  +ᶻ-pos-zsucc zer x = refl _
  +ᶻ-pos-zsucc (pos zero) x = refl _
  +ᶻ-pos-zsucc (pos (succ n)) x = ap zsucc (+ᶻ-pos-zsucc (pos n) x)
  +ᶻ-pos-zsucc (neg zero) x = zsuccpred-id (pos x)
  +ᶻ-pos-zsucc (neg (succ n)) x = zsuccpred-predsucc (neg n +ᶻ pos x) · ap zpred (+ᶻ-pos-zsucc (neg n) x)

  +ᶻ-neg-zpred : (n : ℤ) → (x : ℕ) → zpred (n +ᶻ neg x) == n +ᶻ neg (succ x)
  +ᶻ-neg-zpred zer x = refl _
  +ᶻ-neg-zpred (pos zero) x = zpredsucc-id (neg x)
  +ᶻ-neg-zpred (pos (succ n)) x = zpredsucc-succpred (pos n +ᶻ neg x) · ap zsucc (+ᶻ-neg-zpred (pos n) x)
  +ᶻ-neg-zpred (neg zero) x = refl _
  +ᶻ-neg-zpred (neg (succ n)) x = ap zpred (+ᶻ-neg-zpred (neg n) x)
  
  +ᶻ-comm : (n m : ℤ) → n +ᶻ m == m +ᶻ n
  +ᶻ-comm zer m = +ᶻ-lunit m
  +ᶻ-comm (pos zero) m = +ᶻ-unit-zsucc m
  +ᶻ-comm (pos (succ x)) m = ap zsucc (+ᶻ-comm (pos x) m) · +ᶻ-pos-zsucc m x 
  +ᶻ-comm (neg zero) m = +ᶻ-unit-zpred m
  +ᶻ-comm (neg (succ x)) m = ap zpred (+ᶻ-comm (neg x) m) · +ᶻ-neg-zpred m x

  +-minus : (n : ℤ) → n +ᶻ (- n) == zer
  +-minus zer = refl zer
  +-minus (pos zero) = refl zer
  +-minus (pos (succ x)) =
    begin
      zsucc (pos x +ᶻ neg (succ x)) ==⟨ ap zsucc (inv (+ᶻ-neg-zpred (pos x) x)) ⟩
      zsucc (zpred (pos x +ᶻ neg x)) ==⟨ zsuccpred-id (pos x +ᶻ neg x) ⟩
      pos x +ᶻ neg x ==⟨ +-minus (pos x) ⟩      
      zer
    ∎
  +-minus (neg zero) = refl zer
  +-minus (neg (succ x)) =
    begin
      zpred (neg x +ᶻ pos (succ x)) ==⟨ ap zpred (inv (+ᶻ-pos-zsucc (neg x) x)) ⟩
      zpred (zsucc (neg x +ᶻ pos x)) ==⟨ zpredsucc-id _ ⟩
      neg x +ᶻ pos x ==⟨ +-minus (neg x) ⟩      
      zer
    ∎
  

  -- Decidable equality
  pos-inj : {n m : ℕ} → pos n == pos m → n == m
  pos-inj {n} {.n} (refl .(pos n)) = refl n

  neg-inj : {n m : ℕ} → neg n == neg m → n == m
  neg-inj {n} {.n} (refl .(neg n)) = refl n
  
  z-decEq : decEq ℤ
  z-decEq zer zer = inl (refl zer)
  z-decEq zer (pos x) = inr (λ ())
  z-decEq zer (neg x) = inr (λ ())
  z-decEq (pos x) zer = inr (λ ())
  z-decEq (pos n) (pos m) with (nat-decEq n m)
  z-decEq (pos n) (pos m) | inl p = inl (ap pos p)
  z-decEq (pos n) (pos m) | inr f = inr (f ∘ pos-inj)
  z-decEq (pos n) (neg m) = inr (λ ())
  z-decEq (neg n) zer = inr (λ ())
  z-decEq (neg n) (pos x₁) = inr (λ ())
  z-decEq (neg n) (neg m) with (nat-decEq n m)
  z-decEq (neg n) (neg m) | inl p = inl (ap neg p)
  z-decEq (neg n) (neg m) | inr f = inr (f ∘ neg-inj)

  z-isSet : isSet ℤ
  z-isSet = hedberg z-decEq


  -- Multiplication
  infixl 60 _*ᶻ_
  _*ᶻ_ : ℤ → ℤ → ℤ
  zer *ᶻ m = zer
  pos zero *ᶻ m = m
  pos (succ x) *ᶻ m = (pos x *ᶻ m) +ᶻ m
  neg zero *ᶻ m = - m
  neg (succ x) *ᶻ m = (neg x *ᶻ m) +ᶻ (- m)


  -- Ordering
  _<ᶻ_ : ℤ → ℤ → Type0
  zer <ᶻ zer = ⊥
  zer <ᶻ pos x = ⊤
  zer <ᶻ neg x = ⊥
  pos x <ᶻ zer = ⊥
  pos x <ᶻ pos y = x <ₙ y
  pos x <ᶻ neg y = ⊥
  neg x <ᶻ zer = ⊤
  neg x <ᶻ pos y = ⊤
  neg x <ᶻ neg y = y <ₙ x
