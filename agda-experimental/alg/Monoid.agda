open import Equality

module Monoid where

  record Monoid (A : Set) (ε : A) (_•_ : A → A → A) : Set where
    constructor monoid
    field
      lunit : (a : A) → a • ε ≡ a
      runit : (a : A) → ε • a ≡ a
      assoc : (a b c : A) → (a • b) • c ≡ a • (b • c)

    
  open Monoid public
      
  record Group (A : Set) (ε : A) (_•_ : A → A → A) (inv : A → A) : Set where
    constructor group
    field
      submonoid : Monoid A ε _•_
      linv : (a : A) → (inv a) • a ≡ ε
      rinv : (a : A) → a • (inv a) ≡ ε
  open Group public
