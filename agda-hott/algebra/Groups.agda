{-# OPTIONS --without-K #-}


-- Agda-hott library.
-- Author: Mario Román

-- Groups.  Definition of the algebraic structure of a group.

open import Base

module algebra.Groups where

  record GroupStructure {ℓ} (M : Type ℓ) : Type ℓ where
    constructor group-structure
    field
      -- A group is a monoid
      _*_ : M → M → M
      e : M            
      lunit : ∀ x → (e * x) == x
      runit : ∀ x → (x * e) == x
      assoc : ∀ x y z → (x * (y * z)) == ((x * y) * z)

      -- With inverses
      ginv : M → M
      glinv : ∀ g → (g * ginv g) == e
      grinv : ∀ g → (ginv g * g) == e

  record Group {ℓ} : Type (lsuc ℓ) where
    constructor group
    field
      M : Type ℓ
      str : GroupStructure M
  open Group {{...}} public 
