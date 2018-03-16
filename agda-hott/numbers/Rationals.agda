{-# OPTIONS --without-K #-}

open import Base
open import logic.Hedberg
open import logic.Quotients
open import equality.DecidableEquality
open import numbers.Naturals
open import numbers.Integers

module numbers.Rationals where

  -- Building the rationals from an equivalence relation on pairs of
  -- integers and naturals.
  ℚrel : ℤ × ℕ → ℤ × ℕ → Type0
  ℚrel (a , n) (b , m) = (a *ᶻ pos m) == (b *ᶻ pos n)

  ℚRel : QRel (ℤ × ℕ)
  ℚRel = record { R = ℚrel ; Aset = hedberg (decEqProd z-decEq nat-decEq)
                ; Rprop = λ _ _ → z-isSet _ _ }

  ℚ : Type1
  ℚ = (ℤ × ℕ) / ℚRel

  -- Ordering
  _<ₜ_ : ℚ → ℚ → Type0
  _<ₜ_ = QRel-rec-bi f {!!}
    where
      f : ℤ × ℕ → ℤ × ℕ → Type0
      f (a , n) (b , m) = a *ᶻ pos m <ᶻ b *ᶻ pos n

      welldefined : (x y z t : ℤ × ℕ) → R {{ℚRel}} x y → R {{ℚRel}} z t → f x z == f y t
      welldefined (x1 , x2) (y1 , y2) (z1 , z2) (t1 , t2) r1 r2 = {!!}
      -- ((x1 *ᶻ pos z2) <ᶻ (z1 *ᶻ pos x2)) ==
      -- ((y1 *ᶻ pos t2) <ᶻ (t1 *ᶻ pos y2))
