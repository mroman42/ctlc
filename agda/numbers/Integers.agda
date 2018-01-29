{-# OPTIONS --without-K #-}

open import Base
open import Equality
open import Composition
open import logic.Quotients
open import logic.Hedberg
open import equivalence.Equivalence
open import equality.DecidableEquality
open import equality.DependentProduct
open import numbers.Naturals

module numbers.Integers where

  -- Definition of the integers as a quotient over the naturals
  z-QRelR : ℕ × ℕ → ℕ × ℕ → Type0
  z-QRelR (a , c) (b , d) = (a +ₙ d) == (b +ₙ c)

  z-QRel : QRel (ℕ × ℕ)
  z-QRel = record { R = z-QRelR
                  ; Aset = hedberg (decEqProd nat-decEq nat-decEq)
                  ; Rprop = λ { (a , c) (b , d) → nat-isSet (a +ₙ d) (b +ₙ c) } }

  ℤ : Type1
  ℤ = (ℕ × ℕ) / z-QRel

  -- Inclusion of the natural numbers into the integers
  ntoz : ℕ → ℤ
  ntoz n = [(n , zero)]

  ntoZneg : ℕ → ℤ
  ntoZneg n = [(zero , n)]

  z-zero : ℤ
  z-zero = ntoz 0
  z-one : ℤ
  z-one = ntoz 1

  -- We need to prove that a function on the quotient type is well-defined.
  zsucc : ℤ → ℤ
  zsucc = QRel-rec f welldefined
    where
      f : (ℕ × ℕ) → ℤ
      f (a , b) = [(succ a , b)]
      
      welldefined : (u v : ℕ × ℕ) → R {{z-QRel}} u v → f u == f v
      welldefined (a , c) (b , d) r = Req (ap succ r)

  zpred : ℤ → ℤ
  zpred = QRel-rec f welldefined
    where
      f : (ℕ × ℕ) → ℤ
      f (a , b) = [(a , succ b)]

      welldefined : (u v : ℕ × ℕ) → R {{z-QRel}} u v → f u == f v
      welldefined (a , c) (b , d) r = Req (plus-succ-rs a _ b _ r)

  zsucc-pred-id : (x : ℤ) → zsucc (zpred x) == x
  zsucc-pred-id = QRel-ind f welldefined
    where
      f : (u : ℕ × ℕ) → zsucc (zpred [ u ]) == [ u ]
      f (a , b) = Req (plus-succ-rs zero _ a _ (refl (plus a _)))

      welldefined : (u v : ℕ × ℕ) → (o : R {{z-QRel}} u v)
                  → transport (λ x → zsucc (zpred x) == x) (Req o) (f u) == f v
      welldefined u v o = Rtrunc (zsucc (zpred [ v ])) [ v ] _ _

  zpred-succ-id : (x : ℤ) → zpred (zsucc x) == x
  zpred-succ-id = QRel-ind f welldefined
    where
      f : (u : ℕ × ℕ) → zpred (zsucc [ u ]) == [ u ]
      f (a , b) = Req (plus-succ-rs zero _ a _ (refl (plus a _)))

      welldefined : (u v : ℕ × ℕ) → (o : R {{z-QRel}} u v)
                  → transport (λ x → zpred (zsucc x) == x) (Req o) (f u) == f v
      welldefined u v o = Rtrunc (zpred (zsucc [ v ])) [ v ] _ _

  zequiv-succ : ℤ ≃ ℤ
  zequiv-succ = zsucc , {!!}

  -- Addition
  infixl 60 _+ᶻ_
  _+ᶻ_ : ℤ → ℤ → ℤ
  _+ᶻ_ = QRel-rec f welldefined
    where
      f : (ℕ × ℕ) → (ℤ → ℤ)
      f (zero , zero) = id
      f (zero , succ b) = zpred
      f (succ a , zero) = zsucc
      f (succ a , succ b) = f (a , b)

      welldefined : (u v : ℕ × ℕ) → R {{z-QRel}} u v → f u == f v
      welldefined (zero , zero) (zero , zero) r = funext λ x → refl x
      welldefined (zero , zero) (zero , succ d) ()
      welldefined (zero , zero) (succ b , zero) ()
      welldefined (zero , zero) (succ b , succ .(plus b 0)) (refl .(succ (plus b 0))) = {!!}
      welldefined (zero , succ c) (zero , zero) ()
      welldefined (zero , succ c) (zero , succ .c) (refl .(succ c)) = refl λ x → f (zero , succ c) x
      welldefined (zero , succ c) (succ b , zero) r = {!!}
      welldefined (zero , succ c) (succ b , succ d) r = {!!}
      welldefined (succ a , c) (b , d) r = {!!}
