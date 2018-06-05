{-# OPTIONS --without-K #-}

-- Agda-hott library.
-- Author: Mario Román

-- Propositions.  Propositions as described on the main text. A type
-- is a proposition if we can create a function making any two of its
-- elements equal. We create a type of propositions.

open import Base
open import Equality
open import equality.FunctionExtensionality
open import equality.CartesianProduct
open import logic.Contractible


module logic.Propositions where

  -- A type is a mere proposition if any two inhabitants of the type
  -- are equal
  isProp : ∀{ℓ}  (A : Type ℓ) → Type ℓ
  isProp A = ((x y : A) → x == y)

  -- The type of mere propositions
  hProp : ∀{ℓ} → Type (lsuc ℓ)
  hProp {ℓ} = Σ (Type ℓ) isProp


  -- The dependent function type to proposition types is itself a
  -- proposition.
  piProp : ∀{ℓᵢ ℓⱼ} → {A : Type ℓᵢ} → {B : A → Type ℓⱼ}
         → ((a : A) → isProp (B a)) → isProp ((a : A) → B a)
  piProp props f g = funext λ a → props a (f a) (g a)

  -- The product of propositions is itself a proposition.
  isProp-prod : ∀{ℓᵢ ℓⱼ} → {A : Type ℓᵢ} → {B : Type ℓⱼ}
              → isProp A → isProp B → isProp (A × B)
  isProp-prod p q x y = prodByComponents ((p _ _) , (q _ _))
