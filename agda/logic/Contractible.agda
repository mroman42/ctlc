{-# OPTIONS --without-K #-}

open import Base
open import Equality

module logic.Contractible where

  -- Contractible types. A contractible type is a type such that every
  -- element is equal to a center of contraction.
  isContr : ∀{ℓ}  (A : Type ℓ) → Type ℓ
  isContr A = Σ A (λ a → ((x : A) → a == x))

  module Fibers {ℓ} {A B : Type ℓ} where
    -- The fiber of a map over a point is given by
    fib : (f : A → B) → B → Type ℓ
    fib f b = Σ A (λ a → f a == b)
  
    -- A function applied over the fiber returns the original point
    fib-eq : {f : A → B} → {b : B} → (h : fib f b) → f (fst h) == b
    fib-eq (a , α) = α

    -- Each point is on the fiber of its image
    fib-image : {f : A → B} → {a : A} → fib f (f a)
    fib-image {f} {a} = a , refl (f a)
  open Fibers public
