{-# OPTIONS --without-K #-}
module diaconescu where

record ⊤ : Set where
  instance constructor tt
{-# BUILTIN UNIT ⊤ #-}

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

refl-in : {A : Set} (a : A) → a ≡ a
refl-in a = refl

-- Sigma type
record Σ (S : Set) (T : S → Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Σ public

Σ-elim : {A : Set} {B : A → Set} {P : Set} → Σ A B → (Σ A B → P) → P
Σ-elim (a , b) f = f (a , b)


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

exfalso : {A : Set} → ⊥ → A
exfalso ()


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
    record !Ex (A : Set) (B : A → Set) : Set where
      constructor _!,,_
      field
        !fst : A
        !snd : B !fst
    open !Ex public

  Ex : (A : Set) → (B : A → Set) → Set
  Ex A B = !Ex A B
    
  _,,_ : {A : Set} {B : A → Set} → (a : A) → (b : B a) → Ex A B
  a ,, b = a !,, b

  postulate
    Ex-isProp : {A : Set} {B : A → Set} → isProp (Ex A B)

  -- Recursion principle
  Ex-elim : {A : Set} {B : A → Set} {P : Set} → Ex A B → isProp P → (Σ A B → P) → P
  Ex-elim (a !,, b) _ f = f (a , b)

  syntax Ex A (λ a → e) = ∃ a ∈ A , e

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




LEM : Set₁
LEM = {A : Set} → A ∨ ¬ A

AC : Set₁
AC =
  {X : Set} {A : X → Set} {R : (x : X) → A x → Set}
  → ((x : X) → (a : A x) → isProp (R x a))
  → ((x : X) → ∃ a ∈ (A x), R x a) → ∃ g ∈ ((x : X) → A x), ((x : X) → R x (g x))

diaconescu : AC → LEM
diaconescu ac =
  {!!}
