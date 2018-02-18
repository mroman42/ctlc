{-# OPTIONS --rewriting --type-in-type #-}

open import Equality
open import Base

module Prop where

  isProp : Set → Set
  isProp A = ((x y : A) → x ≡ y)

  record Prop : Set where
    constructor prop
    field
      Prf : Set
      isprop : isProp Prf
  open Prop public


  isProp-prod : {A B : Set} → isProp A → isProp B → isProp (A × B)
  isProp-prod pa pb (a , b) (c , d) with (pa a c) | (pb b d)
  isProp-prod pa pb (a , b) (.a , .b) | refl | refl = refl

  isProp-pi : {A : Set} → {B : A → Set} → ((a : A) → isProp (B a)) → isProp ((a : A) → B a)
  isProp-pi p f g = funext λ x → p x (f x) (g x)

  Not : Prop → Prop
  Not A = prop (Prf A → ⊥) (isProp-pi (λ a x → λ ()))

  Forall : (A : Set) → (A → Prop) → Prop
  Forall A f = prop ((a : A) → Prf (f a)) (isProp-pi (λ a → isprop (f a)))

  ⊥ₚ : Prop
  ⊥ₚ = prop ⊥ (λ x → λ ())

  exfalsoₚ : {A : Set} → Prf ⊥ₚ → A
  exfalsoₚ ()

  ⊤ₚ : Prop
  ⊤ₚ = prop ⊤ λ { ** ** → refl }

  infixr 60 _~>_
  _~>_ : Prop → Prop → Prop
  A ~> B = Forall (Prf A) (λ _ → B)

  infixl 70 _∧_
  _∧_ : Prop → Prop → Prop
  A ∧ B = prop (Prf A × Prf B) (isProp-prod (isprop A) (isprop B))

  infixr 60 _<~>_
  _<~>_ : Prop → Prop → Prop
  A <~> B = (A ~> B) ∧ (B ~> A)

  module Truncation where
    private
      -- Higher inductive type, defined with equalities between any two
      -- members.
      data !∥_∥ (A : Set) : Set where
        !∣_∣ : A → !∥ A ∥
  
    ∥_∥ : (A : Set) → Set
    ∥ A ∥ = !∥ A ∥
  
    ∣_∣ : {X : Set} → X → ∥ X ∥
    ∣ x ∣ = !∣ x ∣
  
    -- Any two elements of the truncated type are equal
    postulate trunc : {A : Set} → isProp ∥ A ∥

    -- Recursion principle
    trunc-rec : {A : Set} {P : Set} → isProp P → (A → P) → ∥ A ∥ → P
    trunc-rec _ f !∣ x ∣ = f x

    ∥_∥ₚ : (A : Set) → Prop
    ∥ A ∥ₚ = prop ∥ A ∥ trunc

    trec : {A : Set} {P : Prop} → (A → Prf P) → Prf (∥ A ∥ₚ ~> P)
    trec {P = P} f = trunc-rec (isprop P) f
  open Truncation public
  

  infixl 70 _∨_
  _∨_ : Prop → Prop → Prop
  A ∨ B = prop (∥ Prf A + Prf B ∥) trunc
  
  ∃ : (A : Set) → (A → Prop) → Prop
  ∃ A f = prop ∥ Σ A (λ a → Prf (f a)) ∥ trunc



  uip : {A : Set} → {a b : A} → isProp (a ≡ b)
  uip {A} {a} {.a} refl refl = refl

  infixl 5 _≡≡_
  _≡≡_ : {A : Set} → (a b : A) → Prop
  a ≡≡ b = prop (a ≡ b) uip


  -- Propositionality as a monad
  _>>=_ : {A B : Set} → ∥ A ∥ → (A → ∥ B ∥) → ∥ B ∥
  a >>= f = trunc-rec trunc f a

  _>>_ : {A B : Set} → ∥ A ∥ → ∥ B ∥ → ∥ B ∥
  _>>_ = λ _ z → z
