{-# OPTIONS --without-K #-}


-- Agda-hott library.
-- Author: Mario Román

-- Interval.  An interval is defined by taking two points (two
-- elements) and a path between them (an element of the equality type).
-- The path is nontrivial.

open import Base
open import Equality

module topology.Interval where

  private
    -- The interval is defined as a type with a nontrivial equality
    -- between its two elements.
    data !I : Set where
      !Izero : !I
      !Ione : !I

  I : Type0
  I = !I

  Izero : I
  Izero = !Izero

  Ione : I
  Ione = !Ione

  postulate seg : Izero == Ione

  -- Induction principle on points.
  I-ind : ∀{ℓ} {A : Type ℓ} → (a b : A) → (p : a == b) → I → A
  I-ind a b p !Izero = a
  I-ind a b p !Ione  = b

  -- Induction principle on paths.
  postulate I-βind : ∀{ℓ} (A : Type ℓ) → (a b : A) → (p : a == b) → ap (I-ind a b p) seg == p
