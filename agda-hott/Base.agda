{-# OPTIONS --without-K #-}

-- Agda-hott library.
-- Author: Mario Román

-- Base.  Basic types of Martin-Löf type theory and some basic
-- functions.

module Base where

  open import base.Universes public
  open import base.Empty public
  open import base.Unit public

  module Basic where
  
    -- Sigma types are a particular case of records, but records can be
    -- constructed using only sigma types. Note that l ⊔ q is the maximum
    -- of two hierarchy levels l and q. This way, we define sigma types in
    -- full generality, at each universe.
    record Σ {ℓᵢ ℓⱼ} (S : Type ℓᵢ)(T : S → Type ℓⱼ) : Type (ℓᵢ ⊔ ℓⱼ) where
      constructor _,_
      field
        fst : S
        snd : T fst
    open Σ public
  
    -- Product type as a particular case of the sigma
    _×_ : ∀{ℓᵢ ℓⱼ} (S : Type ℓᵢ) (T : Type ℓⱼ) → Type (ℓᵢ ⊔ ℓⱼ)
    A × B = Σ A (λ _ → B)

    -- Sum types as inductive types
    data _+_ {ℓᵢ ℓⱼ} (S : Type ℓᵢ) (T : Type ℓⱼ) : Type (ℓᵢ ⊔ ℓⱼ) where
      inl : S → S + T
      inr : T → S + T

    -- Boolean type, two constants true and false
    data Bool : Type0 where
      true : Bool
      false : Bool

    -- Natural numbers are the initial algebra for a constant and a
    -- successor function. The BUILTIN declaration allows us to use
    -- natural numbers in arabic notation.
    data ℕ : Type0 where
      zero : ℕ
      succ : ℕ → ℕ
    {-# BUILTIN NATURAL ℕ #-}

  open Basic public

  -- Identity function
  id : ∀{ℓ} {A : Type ℓ} → A → A
  id a = a

  -- Composition
  _∘_ : ∀{ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {C : Type ℓₖ}
        → (B → C) → (A → B) → (A → C)
  (g ∘ f) z = g (f z)

  -- Equality is defined as an inductive type. Its induction principle
  -- is the J-eliminator.
  data _==_ {ℓ} {A : Type ℓ} : A → A → Type ℓ where
    refl : (a : A) → a == a

  -- Composition of paths
  infixl 50 _·_
  _·_ : ∀{ℓ} {A : Type ℓ}  {a b c : A} → a == b → b == c → a == c
  refl a · q = q
