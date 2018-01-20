{-# OPTIONS --without-K #-}

open import Base
open import Equality

module Homotopies {ℓ} {A : Type ℓ} {P : A → Type ℓ} where

  -- A homotopy is a natural isomorphism between two functions, we will write
  -- f ∼ g when (f x == g x) for all x.
  homotopy : (f g : ((x : A) → P x)) → Type ℓ
  homotopy f g = (x : A) → f x == g x

  _∼_ : (f g : ((x : A) → P x)) → Type ℓ
  f ∼ g = homotopy f g


  -- Homotopy is an equivalence relation
  homotopy-refl : (f : (x : A) → P x) → f ∼ f
  homotopy-refl f x = refl (f x)

  homotopy-simm : (f g : (x : A) → P x) → f ∼ g → g ∼ f
  homotopy-simm f g u x = inv (u x)

  homotopy-comp : (f g h : (x : A) → P x) → f ∼ g → g ∼ h → f ∼ h
  homotopy-comp f g h u v x = (u x)·(v x)
