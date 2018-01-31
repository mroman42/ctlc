{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality
open import equality.DependentProduct
open import logic.Contractible

module logic.Propositions where

  -- A type is a mere proposition if any two inhabitants of the type
  -- are equal
  isProp : ∀{ℓ}  (A : Type ℓ) → Type ℓ
  isProp A = ((x y : A) → x == y)

  -- The type of mere propositions
  hProp : ∀{ℓ} → Type (lsuc ℓ)
  hProp {ℓ} = Σ (Type ℓ) isProp
  
  -- TODO: Truth is the only true mere proposition, any other true
  -- proposition is equivalent to truth.

  piProp : ∀{ℓᵢ ℓⱼ} → {A : Type ℓᵢ} → {B : A → Type ℓⱼ}
         → ((a : A) → isProp (B a))
         → isProp ((a : A) → B a)
  piProp props f g = funext λ a → props a (f a) (g a)
       
