{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Equality

module Base where

  data ⊥ : Set where

  record ⊤ : Set where
    constructor **

  record Σ (S : Set) (T : S → Set) : Set where
    constructor _,_
    field
      fst : S
      snd : T fst
  open Σ public

  _×_ : (S : Set) (T : Set) → Set
  A × B = Σ A (λ _ → B)
  

  data _+_ (S : Set) (T : Set) : Set where
    inl : S → S + T
    inr : T → S + T

  ¬ : Set → Set
  ¬ A = A → ⊥

  exfalso : {A : Set} → ⊥ → A
  exfalso ()

  postulate
    funext : {A : Set} {B : A → Set} → {f g : (a : A) → B a} → ((x : A) → f x ≡ g x) → f ≡ g
  

