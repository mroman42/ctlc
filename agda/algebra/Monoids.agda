{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality
open import logic.Sets

module algebra.Monoids {ℓ} where

  record Monoid : Type (lsuc ℓ) where
    field
      -- Operations of a monoid
      G : Type ℓ         
      GisSet : isSet G
      _<>_ : G → G → G  -- Multiplication function
      e : G             -- Unit element

      -- Axioms of a monoid
      lunit : (x : G) → (e <> x) == x
      runit : (x : G) → (x <> e) == x
      assoc : (x y z : G) → (x <> (y <> z)) == ((x <> y) <> z)
  open Monoid {{...}} public

  -- TODO: Lists are free monoids
  -- TODO: Monoid homomorphisms

  data List (A : Type0) : Type0 where
    [] : List A
    ∷ : A → List A → List A


  
    
