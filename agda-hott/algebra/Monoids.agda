{-# OPTIONS --without-K #-}


-- Agda-hott library.
-- Author: Mario Román

-- Monoid.  Definition of the algebraic structure of a monoid.

open import Agda.Primitive
open import Base
open import Equality
open import logic.Sets

module algebra.Monoids {ℓ} where

  record Monoid : Type (lsuc ℓ) where
    field
      -- Operations of a monoid
      G : Type ℓ         
      GisSet : isSet G
      _<>_ : G → G → G  -- Multiplication function
      e : G             -- Unit element

      -- Axioms of a monoid
      lunit : (x : G) → (e <> x) == x
      runit : (x : G) → (x <> e) == x
      assoc : (x y z : G) → (x <> (y <> z)) == ((x <> y) <> z)
  open Monoid {{...}} public
