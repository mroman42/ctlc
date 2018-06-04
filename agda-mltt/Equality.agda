{-# OPTIONS --rewriting #-}

-- Agda-MLTT library.
-- Author: Mario Román.

-- Equality.  Properties of the equality types in Martin-Löf type
-- theory.  They are derived from the induction principle given by the
-- J-eliminator.  In particular, we can prove theorems on the
-- reflexivity case and they are extended to any other case by the
-- induction principle.


open import Base

module Equality where

  -- Equality types have a groupoid structure.  That is, they can be
  -- composed associatively (by transitivity), each equality has an
  -- inverse (by symmetry) and there is an neutral element
  -- (reflexivity).

  -- Composition of equalities. This can be read as transitivity.
  _·_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  refl · q = q

  -- Inverse of an equality. This can be read as symmetry.
  inv : {A : Set} {a b : A} → a ≡ b → b ≡ a
  inv refl = refl

  -- Equalities are also preserved by functions.
  ap : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
  ap f refl = refl

  -- If two terms are equal, a proof of a proposition instantiated
  -- over one of them is automatically a proof of a proposition
  -- instantiated over the other. Propositions can be transported
  -- along equalities.
  transport : {A : Set} (P : A → Set) {a b : A} → a ≡ b → P a → P b
  transport P refl = λ x → x

  -- Common combinators for equational reasoning. They allow us to
  -- write proofs in an equational style. These versions have been
  -- adapted from the old version of the HoTT-agda library.
  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ :  {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ p1 ⟩ p2 = p1 · p2

  infix  3 _qed
  _qed : {A : Set} (x : A) → x ≡ x
  _qed x = refl

  infix  1 begin_
  begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
  begin_ p = p

  -- A lemma on the equality of a dependent pair. A pair is equal if
  -- its two components are equal. If the second component depends on
  -- the first one, we must transport the component along the
  -- equality.
  Σ-eq : {A : Set} {B : A → Set} → (u v : Σ A B)
    → (p : fst u ≡ fst v)
    → (transport B p (snd u) ≡ snd v)
    → u ≡ v
  Σ-eq (a , b) (.a , .b) refl refl = refl
