{-# OPTIONS --without-K #-}

-- Agda-hott library.
-- Author: Mario Román

-- Unit.  A type with a single element, representing truth.

open import base.Universes

module base.Unit {ℓ} where

  -- A record without fields is the unit type with a single
  -- constructor.
  record ⊤ : Type ℓ where
    constructor ★
