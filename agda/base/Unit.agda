{-# OPTIONS --without-K #-}

open import base.Universes

module base.Unit {ℓ} where

  -- A record without constructors is the unit type.
  record ⊤ : Type ℓ where
    constructor ★
