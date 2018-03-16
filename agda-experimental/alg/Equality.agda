
module Equality where

  -- Equality
  infix 4 _≡_
  data _≡_ {A : Set} : A → A → Set where
    refl : {a : A} → a ≡ a

  -- Concatenation of paths
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
