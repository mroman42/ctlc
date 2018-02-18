{-# OPTIONS --without-K #-}

open import Base

module EquationalReasoning {ℓᵢ} {A : Type ℓᵢ} where

  -- Common combinators for equational reasoning. They allow us to
  -- write proof in an equational style. These versions have been
  -- adapted from the old version of the HoTT-agda library.
  infixr 2 _==⟨_⟩_
  _==⟨_⟩_ :  (x : A) {y z : A} → x == y → y == z → x == z
  _ ==⟨ p1 ⟩ p2 = p1 · p2

  infix  3 _∎
  _∎ : (x : A) → x == x
  _∎ = refl

  infix  1 begin_
  begin_ : {x y : A} → x == y → x == y
  begin_ p = p
