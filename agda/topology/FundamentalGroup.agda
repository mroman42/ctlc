{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality
open import logic.Truncation
open import algebra.Groups

module topology.FundamentalGroup {ℓ} where

  -- Fundamental group
  π₁ : (A : Type ℓ) → (a : A) → Group {ℓ}
  π₁ A a = ∥ a == a ∥ , {!!}
