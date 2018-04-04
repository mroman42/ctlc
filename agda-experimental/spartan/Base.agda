{-# OPTIONS --rewriting #-}

module Base where

record ⊤ : Set where
  instance constructor tt

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
