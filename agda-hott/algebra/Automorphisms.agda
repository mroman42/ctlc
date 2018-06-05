{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality
open import equivalence.Equivalence
open import algebra.Groups

module algebra.Automorphisms {ℓ} {A : Type ℓ} where

  automorphisms : Type ℓ
  automorphisms = A ≃ A
