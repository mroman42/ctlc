{-# OPTIONS --without-K #-}

open import Base
open import Equality
open import Composition
open import logic.Quotients
open import logic.Hedberg
open import equivalence.Equivalence
open import equivalence.Quasiinverses
open import equality.DecidableEquality
open import equality.FunctionExtensionality
open import numbers.Naturals


module numbers.Integers2 where

  -- Definition of the integers as a quotient over the naturals
  z-rel : ℕ × ℕ → ℕ × ℕ → Type0
  z-rel (a , c) (b , d) = (a +ₙ d) == (b +ₙ c)

  z-QRel : QRel (ℕ × ℕ)
  z-QRel = record { R = z-rel
                  ; Aset = hedberg (decEqProd nat-decEq nat-decEq)
                  ; Rprop = λ { _ _ → nat-isSet _ _ } }

  ℤ : Type1
  ℤ = (ℕ × ℕ) / z-QRel

  -- Properties of the relation
  -- z-rel-plus-both : (o a b : ℕ) → z-rel (a , b) (o +ₙ a , o +ₙ b)
  -- z-rel-plus-both zero     a b = refl (plus a b)
  -- z-rel-plus-both (succ o) a b = {!!}


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
      f (a , b) = [ a , (succ b) ]

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
  zequiv-succ = qinv-≃ zsucc (zpred , (zsucc-pred-id , zpred-succ-id))

  -- zpaths : ∀{ℓ} {A : Type ℓ} {a : A} → (p : a == a) → (n : ℤ) → a == a
  -- zpaths {a = a} p = {!!}
  --   where
  --     f : (u : ℕ × ℕ) → a == a
  --     f (n , m) = {!!}

  --     welldefined : (u v : ℕ × ℕ) → R {{z-QRel}} u v → f u == f v
  --     welldefined (a , c) (b , d) r = {!!}
