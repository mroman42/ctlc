{-# OPTIONS --without-K #-}

open import Base

module Equality where

  -- Equality is defined as an inductive type
  data _==_ {ℓ} {A : Set ℓ} : A → A → Type ℓ where
    refl : (a : A) → a == a


  -- Types are higher groupoids.
  -- Inverse of a path
  inv : ∀{ℓ} {A : Type ℓ}  {a b : A} → a == b → b == a
  inv (refl a) = refl a

  -- Composition of paths
  infix 50 _·_
  _·_ : ∀{ℓ} {A : Type ℓ}  {a b c : A} → a == b → b == c → a == c
  refl a · q = q

  -- Transport
  transport : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ}  (P : A → Type ℓⱼ) {a b : A} → a == b → P a → P b
  transport P (refl a) = id
  

  -- Functions are functors to equalities
  ap : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ}  {a b : A} → (f : A → B) →
       a == b → f a == f b
  ap f (refl a) = refl (f a)

  apd : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ}  {P : A → Type ℓⱼ} {a b : A} → (f : (a : A) → P a) →
        (p : a == b) → transport P p (f a) == f b 
  apd f (refl a) = refl (f a)

  happly : ∀{ℓ} {A B : Type ℓ} {f g : A → B} → f == g → ((x : A) → f x == g x)
  happly (refl f) x = refl (f x)
