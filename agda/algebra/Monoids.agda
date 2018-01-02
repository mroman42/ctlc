{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality
open import numbers.Naturals

module algebra.Monoids where

  record Monoid : Type1 where
    field
      -- Operations of a monoid
      G : Type0        -- Carrier, TODO: should be a set
      _⋆_ : G → G → G  -- Multiplication function
      e : G            -- Unit element

      -- Axioms of a monoid
      lunit : (x : G) → (e ⋆ x) == x
      runit : (x : G) → (x ⋆ e) == x
      assoc : (x y z : G) → (x ⋆ (y ⋆ z)) == ((x ⋆ y) ⋆ z)


  -- Naturals form a monoid with addition
  ℕ-plus-monoid : Monoid
  ℕ-plus-monoid = record
    { G = ℕ
    ; _⋆_ = plus
    ; e = zero
    ; lunit = plus-lunit
    ; runit = plus-runit
    ; assoc = plus-assoc
    }
  

  -- TODO: Lists are free monoids
  -- TODO: Monoid homomorphisms

  data List (A : Type0) : Type0 where
    [] : List A
    ∷ : A → List A → List A


  
    
