{-# OPTIONS --type-in-type #-}

open import base.Base

module base.Prop where

isProp : Set → Set
isProp A = ((x y : A) → x ≡ y)

prod-isProp : {A B : Set} → isProp A → isProp B → isProp (A × B)
prod-isProp pa pb (a , b) (c , d) with (pa a c) | (pb b d)
prod-isProp pa pb (a , b) (.a , .b) | refl | refl = refl

pi-isProp : {A : Set} → {B : A → Set} → ((a : A) → isProp (B a)) → isProp ((a : A) → B a)
pi-isProp p f g = funext λ x → p x (f x) (g x)

not-isProp : {A : Set} → isProp (¬ A)
not-isProp = pi-isProp (λ a x → λ ())

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
open Truncation public
  

module Exists where
  private
    record !∃ (A : Set) (B : A → Set) : Set where
      constructor _!,,_
      field
        !fst : A
        !snd : B !fst
    open !∃ public

  ∃ : (A : Set) → (B : A → Set) → Set
  ∃ A B = !∃ A B
    
  _,,_ : {A : Set} {B : A → Set} → (a : A) → (b : B a) → ∃ A B
  a ,, b = a !,, b

  postulate
    ∃-isProp : {A : Set} {B : A → Set} → isProp (∃ A B)

  -- Recursion principle
  ∃-elim : {A : Set} {B : A → Set} {P : Set} → ∃ A B → isProp P → (Σ A B → P) → P
  ∃-elim (a !,, b) _ f = f (a , b)

open Exists public

module Or where
  private
    data _!∨_ (A B : Set) : Set where
      !inl : A → A !∨ B
      !inr : B → A !∨ B

  _∨_ : (A B : Set) → Set
  A ∨ B = A !∨ B

  rinl : {A B : Set} → A → A ∨ B
  rinl a = !inl a

  rinr : {A B : Set} → B → A ∨ B
  rinr b = !inr b

  postulate
    ∨-isProp : {A B : Set} → isProp (A ∨ B)

  -- Recursion principle
  ∨-elim : {A B P : Set} → A ∨ B → isProp P → ((A ⊎ B) → P) → P
  ∨-elim (!inl x) _ f = f (inl x)
  ∨-elim (!inr x) _ f = f (inr x)
open Or public

uip : {A : Set} → {a b : A} → isProp (a ≡ b)
uip {A} {a} {.a} refl refl = refl
