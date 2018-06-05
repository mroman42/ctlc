{-# OPTIONS --without-K #-}

-- Agda-hott library.
-- Author: Mario Román

-- Equality.  Properties and structure of the equality type.

open import Base
open import EquationalReasoning

module Equality where

  -- Types are higher groupoids.  If we see equalities as paths, this
  -- is the inverse of a path. If we see equalities classically, this
  -- is the symmetric property of equality.
  inv : ∀{ℓ} {A : Type ℓ}  {a b : A}
    → a == b
    → b == a
  inv (refl a) = refl a
  
  -- Functions are functors to equalities.  In other words, functions
  -- preserve equalities.
  ap : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ}  {a b : A} → (f : A → B)
    →   a == b
    → f a == f b
  ap f (refl a) = refl (f a)


  -- Some properties on the groupoid structure of equalities.
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
    
    ·-cancellation : {a : A} (p : a == a) → (q : a == a) → p · q == p → q == refl a
    ·-cancellation {a} p q α =
      begin
        q                   ==⟨ ap (_· q) (inv (·-linv p)) ⟩
        inv p · p · q       ==⟨ (·-assoc (inv p) _ _) ⟩
        inv p · (p · q)     ==⟨ (ap (inv p ·_) α) ⟩
        inv p · p           ==⟨ ·-linv p ⟩
        refl a
      ∎
  open ·-Properties public


  -- When we transport a proof of (P a) over an equality (a == b), we
  -- get a proof of (P b).
  module Transport {ℓᵢ} {A : Type ℓᵢ} where
    -- Transport
    transport : ∀{ℓⱼ} (P : A → Type ℓⱼ) {a b : A}
      → a == b
      → P a
      → P b
    transport P (refl a) = id

    -- Some lemmas on the transport operation.
    transport-concat-r : {a : A} {x y : A} → (p : x == y) → (q : a == x) →
      transport (λ x → a == x) p q == q · p
    transport-concat-r (refl a) q = ·-runit q

    transport-concat-l : {a : A} {x y : A} → (p : x == y) → (q : x == a) →
      transport (λ x → x == a) p q == (inv p) · q
    transport-concat-l (refl a) q = refl q

    transport-concat : {x y : A} → (p : x == y) → (q : x == x) →
      transport (λ x → x == x) p q == (inv p) · q · p
    transport-concat (refl a) q = ·-runit q    

    transport-eq-fun : ∀{ℓⱼ} {B : Type ℓⱼ} (f g : A → B) {x y : A} (p : x == y) (q : f x == g x)
                      → transport (λ z → f z == g z) p q == inv (ap f p) · q · (ap g p)
    transport-eq-fun f g (refl a) q = ·-runit q

    transport-comp : ∀{ℓⱼ} {a b c : A} {P : A → Type ℓⱼ} (p : a == b) (q : b == c)
                     → ((transport P q) ∘ (transport P p)) == transport P (p · q)
    transport-comp {P = P} (refl a) q = refl (transport P q)

    transport-comp-h : ∀{ℓⱼ} {a b c : A} {P : A → Type ℓⱼ} (p : a == b) (q : b == c) (x : P a)
                     → ((transport P q) ∘ (transport P p)) x == transport P (p · q) x
    transport-comp-h {P = P} (refl a) q x = refl (transport P q x)

    -- A shorter notation for transport.
    _✶ : ∀{ℓⱼ} {P : A → Type ℓⱼ} {a b : A} → a == b → P a → P b
    _✶ = transport _
  open Transport public

  -- More properties and lemmas on equality, transporting and function
  -- application.
  ap-id : ∀{ℓᵢ} {A : Type ℓᵢ} {a b : A} (p : a == b) → ap id p == p
  ap-id (refl a) = refl (refl a)

  ap-comp : ∀{ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {C : Type ℓₖ}  {a b : A}
          → (f : A → B) → (g : B → C) → (p : a == b)
          → ap g (ap f p) == ap (g ∘ f) p
  ap-comp f g (refl a) = refl (refl (g (f a)))

  ap-const : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {C : Type ℓⱼ} {a b : A} {c : C} (p : a == b)
           → ap (λ _ → c) p == refl c
  ap-const {c = c} (refl a) = refl (refl c)

  ap-· : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {a b c : A}
       → (f : A → B) → (p : a == b) → (q : b == c)
       → ap f (p · q) == ap f p · ap f q
  ap-· f (refl a) q = refl (ap f q)

  ap-inv : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {a b : A}
         → (f : A → B) → (p : a == b)
         → ap f (inv p) == inv (ap f p)
  ap-inv f (refl a) = refl (refl (f a))
  
  transport-eq-fun-l : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {b : B} (f : A → B) {x y : A}
                       → (p : x == y) (q : f x == b)
                       → transport (λ z → f z == b) p q == inv (ap f p) · q
  transport-eq-fun-l {b = b} f p q =
    begin
      transport (λ z → f z == b) p q      ==⟨ transport-eq-fun f (λ _ → b) p q ⟩
      inv (ap f p) · q · ap (λ _ → b) p   ==⟨ ap (inv (ap f p) · q ·_) (ap-const p) ⟩
      inv (ap f p) · q · refl b           ==⟨ inv (·-runit _) ⟩
      inv (ap f p) · q
    ∎

  transport-eq-fun-r : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} {b : B} (g : A → B) {x y : A}
                       → (p : x == y) (q : b == g x)
                       → transport (λ z → b == g z) p q == q · (ap g p)
  transport-eq-fun-r {b = b} g p q =
    begin
      transport (λ z → b == g z) p q      ==⟨ transport-eq-fun (λ _ → b) g p q ⟩
      inv (ap (λ _ → b) p) · q · ap g p   ==⟨ ·-assoc (inv (ap (λ _ → b) p)) q (ap g p) ⟩
      inv (ap (λ _ → b) p) · (q · ap g p) ==⟨ ap (λ u → inv u · (q · ap g p)) (ap-const p) ⟩
      (q · ap g p) 
    ∎

  transport-inv-l : ∀{ℓ} {A B : Type ℓ} → (p : A == B) → (b : B)
                → transport (λ v → v) p (transport (λ v → v) (inv p) b) == b
  transport-inv-l (refl a) b = refl b

  transport-inv-r : ∀{ℓ} {A B : Type ℓ} → (p : A == B) → (a : A)
                → transport (λ v → v) (inv p) (transport (λ v → v) p a) == a
  transport-inv-r (refl a) b = refl b

  transport-family : ∀{ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {P : B → Type ℓₖ}
                   → {f : A → B} → {x y : A} → (p : x == y) → (u : P (f x))
                   → transport (P ∘ f) p u == transport P (ap f p) u
  transport-family (refl a) u = refl u
  
  transport-fun : ∀{ℓᵢ ℓⱼ ℓₖ} {X : Type ℓᵢ} {x y : X} {A : X → Type ℓⱼ} {B : X → Type ℓₖ}
                  → (p : x == y) → (f : A x → B x)
                  → transport (λ x → (A x → B x)) p f == (λ x → transport B p (f (transport A (inv p) x)))
  transport-fun (refl a) f = refl f

  apd : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ}  {P : A → Type ℓⱼ} {a b : A}
      → (f : (a : A) → P a) → (p : a == b)
      → transport P p (f a) == f b
  apd f (refl a) = refl (f a)
