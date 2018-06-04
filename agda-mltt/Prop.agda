open import Base

-- Agda-MLTT library.
-- Author: Mario Román.

-- Prop.  Proposition types. A type is a proposition if we can
-- construct a function that provides an equality between any two of
-- its elements. We define propositional truncation and some truncated
-- logical connectives explicitly hoping to provide clarity on how
-- these types can be constructed inside the system.

module Prop where

-- Definition of Proposition.
isProp : Set → Set
isProp A = ((x y : A) → x ≡ y)

-- The product of two propositions is itself a proposition.
prod-isProp : {A B : Set} → isProp A → isProp B → isProp (A × B)
prod-isProp pa pb (a , b) (c , d) with (pa a c) | (pb b d)
prod-isProp pa pb (a , b) (.a , .b) | refl | refl = refl

-- The implication of a family of propositions is itself a proposition.
pi-isProp : {A : Set} → {B : A → Set} → ((a : A) → isProp (B a)) → isProp ((a : A) → B a)
pi-isProp p f g = funext λ x → p x (f x) (g x)

-- The negation of a proposition is a proposition.
not-isProp : {A : Set} → isProp (¬ A)
not-isProp = pi-isProp (λ a x → λ ())


postulate
  -- We say that two propositions are equal if they follow from each
  -- other.  This notion of equality is called propositional
  -- extensionality.
  propext : {A B : Set} → isProp A → isProp B → (A → B) → (B → A) → A ≡ B


module Truncation where
  -- A type A may have multiple distinct elements, witnessing
  -- different proofs of the same fact. We can, however truncate a
  -- type A into a proposition ∥A∥ by postulating that any two of its
  -- elements must be equal.
  
  private
    -- This is an instance of a higher inductive type, defined with
    -- equalities between any two members. We implement it using
    -- private constuctors (this is called Dan Licata's trick in
    -- literature).
    data !∥_∥ (A : Set) : Set where
      !∣_∣ : A → !∥ A ∥

  -- Constructor of a truncated type.
  ∥_∥ : (A : Set) → Set
  ∥ A ∥ = !∥ A ∥

  -- If x is an element of A, then |x| is an element of its truncated
  -- type. Note, however, that |x|=|y| for any two, potentially
  -- different x,y:A.
  ∣_∣ : {X : Set} → X → ∥ X ∥
  ∣ x ∣ = !∣ x ∣
  
  -- We postulate that any two elements of the truncated type are
  -- equal. 
  postulate trunc : {A : Set} → isProp ∥ A ∥

  -- Recursion principle for truncated types. This is directly derived
  -- from the adjunction described in the text.
  trunc-rec : {A : Set} {P : Set} → isProp P
   → ( A   →  P)
     -----------
   → ∥ A ∥ →  P
  trunc-rec _ f !∣ x ∣ = f x

  -- An easier-to-read variant of the recursion principle.
  trunc-elim : {A : Set} {P : Set} → ∥ A ∥ → isProp P → (A → P) → P
  trunc-elim = λ z z₁ z₂ → trunc-rec z₁ z₂ z
open Truncation public
  

module Exists where
  -- The existential quantifier, in a classical sense, arises as a
  -- propositional truncation of the constructive existential
  -- quantifier.
  private
    -- The existential quantifier is defined mirroring the dependent
    -- pair type. This is again an instance of a higher inductive
    -- type.
    record !Ex (A : Set) (B : A → Set) : Set where
      constructor _!,,_
      field
        !fst : A
        !snd : B !fst
    open !Ex public

  -- Type constructor.
  Ex : (A : Set) → (B : A → Set) → Set
  Ex A B = !Ex A B

  -- Term constructor. Takes a term a : A and a proof of (B a), and
  -- produces a proof of ∃ a : A, (B a).
  _,,_ : {A : Set} {B : A → Set} → (a : A) → (b : B a) → Ex A B
  a ,, b = a !,, b

  postulate
    -- We truncate the term by postulating that it is a proposition.
    Ex-isProp : {A : Set} {B : A → Set} → isProp (Ex A B)

  -- Recursion principle for existential quantifiers.
  Ex-elim : {A : Set} {B : A → Set} {P : Set} → Ex A B → isProp P → (Σ A B → P) → P
  Ex-elim (a !,, b) _ f = f (a , b)

  -- Special syntax for quantifiers.
  syntax Ex A (λ a → e) = ∃ a ∈ A , e

open Exists public



module Or where
  -- The existential disjunction, in a classical sense, arises as a
  -- propositional truncation of the constructive pair of types. It is
  -- defined following the same rules and truncating the resulting
  -- type.
  private
    data _!∨_ (A B : Set) : Set where
      !inl : A → A !∨ B
      !inr : B → A !∨ B

  -- Type constructor.
  _∨_ : (A B : Set) → Set
  A ∨ B = A !∨ B

  -- Term constructors.
  rinl : {A B : Set} → A → A ∨ B
  rinl a = !inl a

  rinr : {A B : Set} → B → A ∨ B
  rinr b = !inr b

  postulate
    -- We truncate the type by postulating that it must be a
    -- proposition.
    ∨-isProp : {A B : Set} → isProp (A ∨ B)

  -- Recursion principle.
  ∨-elim : {A B P : Set} → A ∨ B → isProp P → ((A ⊎ B) → P) → P
  ∨-elim (!inl x) _ f = f (inl x)
  ∨-elim (!inr x) _ f = f (inr x)
open Or public


-- Uniqueness of identity proofs, or Axiom K.  We choose to allow this
-- rule in our theory inside this library in order to ease some
-- proofs, but it will be forbidden inside the homotopy-theoretical
-- version.
uip : {A : Set} → {a b : A} → isProp (a ≡ b)
uip {A} {a} {.a} refl refl = refl
