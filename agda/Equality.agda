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
  infixl 50 _·_
  _·_ : ∀{ℓ} {A : Type ℓ}  {a b c : A} → a == b → b == c → a == c
  refl a · q = q

  

  module Transport {ℓᵢ} {A : Type ℓᵢ} where
    -- Transport
    transport : ∀{ℓⱼ} (P : A → Type ℓⱼ) {a b : A} → a == b → P a → P b
    transport P (refl a) = id

    -- Lemmas on transport
    transport-concat : {a : A} {x y : A} → (p : x == y) → (q : a == x) →
      transport (λ x → a == x) p q == q · p
    transport-concat (refl a) (refl .a) = refl (refl a)

    -- Notation for transport
    _✶ : ∀{ℓⱼ} {P : A → Type ℓⱼ} {a b : A} → a == b → P a → P b
    _✶ = transport _
  open Transport public
  
  -- Functions are functors to equalities
  ap : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ}  {a b : A} → (f : A → B) →
       a == b → f a == f b
  ap f (refl a) = refl (f a)

  apd : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ}  {P : A → Type ℓⱼ} {a b : A} → (f : (a : A) → P a) →
        (p : a == b) → transport P p (f a) == f b 
  apd f (refl a) = refl (f a)


  module ·-Properties {ℓ} {A : Type ℓ} where
    ·-runit : {a b : A} (p : a == b) → p == p · (refl b)
    ·-runit (refl a) = refl (refl a)
  
    ·-lunit : {a b : A} (p : a == b) → p == (refl _) · p
    ·-lunit (refl a) = refl (refl a)
  
    ·-assoc : {a b c d : A} (p : a == b) → (q : b == c) → (r : c == d) →
      (p · q) · r == p · (q · r)
    ·-assoc (refl a) q r = refl (q · r)
  
    ·-linv : {a b : A} (p : a == b) → (inv p) · p == refl b
    ·-linv (refl a) = refl (refl a)
    
    ·-rinv : {a b : A} (p : a == b) → p · (inv p) == refl a
    ·-rinv (refl a) = refl (refl a)
  
    -- TODO: Equational reasoning
    ·-cancellation : {a : A} (p : a == a) → (q : a == a) → p · q == p → q == refl a
    ·-cancellation p q α = ap (_· q) (inv (·-linv p)) ·
                                   (·-assoc (inv p) _ _) ·
                                   (ap (inv p ·_) α) ·
                                   (·-linv p)
  open ·-Properties public
