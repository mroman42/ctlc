{-# OPTIONS --without-K #-}


-- Agda-hott library.
-- Author: Mario Román

-- Dyadic.  A basic implementation of dyadic numbers inside Homotopy
-- Type Theory, please refer to the agda-mltt library for a complete
-- implementation.

open import Base
open import logic.Hedberg
open import logic.Quotients
open import equality.DecidableEquality
open import numbers.Naturals
open import numbers.Integers

module numbers.Dyadic {ℓ} where

   iseven : ℤ → Type (lsuc ℓ)
   iseven zer = ⊤
   iseven (pos zero) = ⊥
   iseven (pos (succ zero)) = ⊤
   iseven (pos (succ (succ x))) = iseven (pos x)
   iseven (neg zero) = ⊥
   iseven (neg (succ zero)) = ⊤
   iseven (neg (succ (succ x))) = iseven (neg x)

   iseven-dec : (z : ℤ) → (iseven z) + ¬ (iseven z)
   iseven-dec zer = inl ★
   iseven-dec (pos zero) = inr (λ ())
   iseven-dec (pos (succ zero)) = inl ★
   iseven-dec (pos (succ (succ x))) = iseven-dec (pos x)
   iseven-dec (neg zero) = inr (λ ())
   iseven-dec (neg (succ zero)) = inl ★
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

   normalized : ℤ → ℕ → Type (lsuc ℓ)
   normalized mnt zero = ⊤
   normalized mnt (succ exp) = ¬ (iseven mnt)

   record Dyadic : Type (lsuc ℓ) where
     constructor dyadic
     field
       mnt : ℤ
       exp : ℕ
       norm : normalized mnt exp

   normalize : ℤ → ℕ → Dyadic
   normalize m zero = dyadic m zero ★
   normalize m (succ e) with (iseven-dec m)
   normalize m (succ e) | inr x = dyadic m (succ e) x
   normalize m (succ e) | inl x = normalize (div2 m x) e



   -- Operations on dyadics
   dzero : Dyadic
   dzero = dyadic zer zero ★

   infixl 60 _+ᵈ_
   _+ᵈ_ : Dyadic → Dyadic → Dyadic
   dyadic dm de dn +ᵈ dyadic em ee en = normalize ((dm *ᶻ exp2 ee) +ᶻ (exp2 de *ᶻ em)) (de +ₙ ee)
