{-# OPTIONS --rewriting #-}

module base.Base where

open import Agda.Builtin.Unit public
open import Agda.Builtin.Bool public
open import Agda.Builtin.Nat public renaming (Nat to ℕ ; suc to succ ; _+_ to _+ⁿ_)
open import Agda.Builtin.Int public renaming (Int to ℤ)
open import Agda.Builtin.Float public
open import Agda.Builtin.List public
open import Agda.Builtin.Char public
open import Agda.Builtin.String public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Reflection public

{-# BUILTIN REWRITE _≡_ #-}

refl-in : {A : Set} (a : A) → a ≡ a
refl-in a = refl

-- Sigma type
record Σ (S : Set) (T : S → Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Σ public


-- Product type
_×_ : (S : Set) (T : Set) → Set
A × B = Σ A (λ _ → B)

-- Sum type
data _⊎_ (S : Set) (T : Set) : Set where
  inl : S → S ⊎ T
  inr : T → S ⊎ T


-- Function extensionality
postulate
  funext : {A : Set} {B : A → Set} → {f g : (a : A) → B a}
    → ((x : A) → f x ≡ g x) → f ≡ g


-- Negation and empty type
data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥

exfalso : {A : Set} → ⊥ → A
exfalso ()
