{-# OPTIONS --without-K #-}

open import Base
open import Equality
open import logic.Quotients
open import logic.Hedberg
open import equality.DecidableEquality
open import numbers.Naturals renaming (plus to _N+_)

module numbers.Integers where

  -- Definition of the integers as a quotient over the naturals
  z-QRelR : ℕ × ℕ → ℕ × ℕ → Type0
  z-QRelR (a , c) (b , d) = (a N+ d) == (c N+ d)

  z-QRel : QRel (ℕ × ℕ)
  z-QRel = record { R = z-QRelR
                  ; Aset = hedberg (decEqProd nat-decEq nat-decEq)
                  ; Rprop = λ { (a , c) (b , d) → nat-isSet (a N+ d) (c N+ d) } }

  ℤ : Type1
  ℤ = (ℕ × ℕ) / z-QRel

  -- Inclusion of the natural numbers into the integers
  Zpos : ℕ → ℤ
  Zpos n = [(n , zero)]

  Zneg : ℕ → ℤ
  Zneg n = [(zero , n)]

  Zzero : ℤ
  Zzero = [(zero , zero)]
