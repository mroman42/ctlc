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
