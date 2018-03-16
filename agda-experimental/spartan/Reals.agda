module Reals where

open import Base
open import Booleans
open import Equality
open import Prop

postulate
  F : Set
  zero : F
  one : F
  _+_ : F → F → F
  _*_ : F → F → F
  _<_ : F → F → Bool

infixl 30 _+_
infixl 35 _*_
infix 6 _<_

postulate
  -- Algebraic structure
  +comm : (a b : F) → a + b ≡ b + a
  +assoc : (a b c : F) → a + (b + c) ≡ a + b + c
  +zero : (a : F) → zero + a ≡ a

  *comm : (a b : F) → a * b ≡ b * a
  *assoc : (a b c : F) → a * (b * c) ≡ a * b * c
  *one : (a : F) → one * a ≡ a
  *distr : (a b c : F) → a * (b + c) ≡ a * b + a * c

  -- Ordered field
  <trans : (a b c : F) → a < b ≡ true → b < c ≡ true → a < c ≡ true

  <one : zero < one ≡ true
  <plus : (a b c : F) → (a + c) < (b + c) ≡ a < b
  <mult : (a b c : F) → zero < a ≡ true → a * b < a * c ≡ b < c

postulate
  -- Half
  half : F
  <half : zero < half ≡ true
  +half : half + half ≡ one


<halfone : half < one ≡ true
<halfone rewrite
  inv (+zero half)
  | inv +half
  | <plus zero half half
  | <half
  = refl

<halfpos : ∀ f
  → zero < f ≡ true
  -----------------
  → zero < half * f ≡ true
<halfpos f p -- rewrite
  -- <mult half zero f ()
  = {!!}

<halfless : ∀ f
  → zero < f ≡ true
  -----------------------
  → half * f < f ≡ true
<halfless f p = {!!}




--------------------------------------------------------
--------------------------------------------------------
--- REALS ----------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
record ℝ⁺ : Set₁ where
  field
    -- Dedekind cut
    cut : F → Set
    propositional : (f : F) → isProp (cut f)
    bounded : ∃ f ∈ F , cut f
    rounded1 : (f : F) → cut f → ∃ r ∈ F , ((r < f ≡ true) × cut r)
    rounded2 : (f : F) → ∃ r ∈ F , ((r < f ≡ true) × cut r) → cut f



real0 : ℝ⁺
real0 = record
  { cut = λ x → zero < x ≡ true
  ; propositional = λ { f → uip }
  ; bounded = one ,, <one
  ; rounded1 = λ f x → (half * f) ,, (<halfless f x , <halfpos f x)
  ; rounded2 = λ f x → Ex-elim x uip λ { (r , (α , β)) → <trans zero r f β α }
  }
