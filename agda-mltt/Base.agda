{-# OPTIONS --without-K #-}

-- Agda-MLTT library.
-- Author: Mario Román.

-- Base.  Basic definitions for Martin-Löf type theory, elimination
-- principles, induction principles and some basic lemmas.

module Base where

-- The terminal type with a single constructor.
record ⊤ : Set where
  instance constructor tt
{-# BUILTIN UNIT ⊤ #-}


-- The initial type, without any constructors.
data ⊥ : Set where

-- Definition of negation.
¬ : Set → Set
¬ A = A → ⊥


-- Definition of equality inside as an inductive type. Its induction
-- principle is the J-elimination rule described in (4.5.2).
infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

-- Explicit reflexivity
refl-in : {A : Set} (a : A) → a ≡ a
refl-in a = refl


-- Definition of the sigma type as a record with two constructors.
-- Its elimination principle can be directly derived from the
-- definition.
record Σ (S : Set) (T : S → Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Σ public

Σ-elim : {A : Set} {B : A → Set} {P : Set} → Σ A B → (Σ A B → P) → P
Σ-elim (a , b) f = f (a , b)

-- Product type, as a particular case of a Sigma type over a constant
-- family of types.
_×_ : (S : Set) (T : Set) → Set
A × B = Σ A (λ _ → B)

-- Sum type.  It is defined explicitly as an inductive type with two
-- constructors.
data _⊎_ (S : Set) (T : Set) : Set where
  inl : S → S ⊎ T
  inr : T → S ⊎ T


-- Function extensionality. We postulate that two functions are equal
-- if they take equal inputs into equal outputs.
postulate
  funext : {A : Set} {B : A → Set} → {f g : (a : A) → B a}
    → ((x : A) → f x ≡ g x) → f ≡ g


-- From falsehood, anything follows.
exfalso : {A : Set} → ⊥ → A
exfalso ()
