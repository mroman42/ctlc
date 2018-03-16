{-# OPTIONS --rewriting #-}

module Equality where

  -- Definition of equality
  infix 5 _≡_
  data _≡_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where
      refl : {a : A} → a ≡ a
  {-# BUILTIN EQUALITY _≡_ #-}
  {-# BUILTIN REWRITE _≡_ #-}

  ap : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
  ap f refl = refl

  inv : {A : Set} {a b : A} → a ≡ b → b ≡ a
  inv refl = refl

  _·_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  refl · q = q

   -- Common combinators for equational reasoning. They allow us to
  -- write proof in an equational style. These versions have been
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
