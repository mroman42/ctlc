{-# OPTIONS --without-K #-}


-- Agda-hott library.
-- Author: Mario Román

-- Relation.  Logical relations in terms of Propositions.

open import Agda.Primitive
open import Base
open import Equality
open import logic.Propositions
open import logic.Sets

module logic.Relation where

  record Rel {ℓ} (A : Type ℓ) : Type (lsuc ℓ) where
    field
      R : A → A → Type ℓ
      Rprop : (a b : A) → isProp (R a b)
  open Rel {{...}} public
