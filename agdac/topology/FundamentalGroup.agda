{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality
open import logic.SetTruncation
open import logic.SetTruncationLemmas
open import logic.HLevels
open import equivalence.EquivalenceSet
open import algebra.Groups

module topology.FundamentalGroup {ℓ} where

  -- Structure of paths in a truncated set
  module PathStructure where
    infixl 50 _π·_
    _π·_ : {A : Type ℓ} {a : A} → ∥ a == a ∥₀ → ∥ a == a ∥₀ → ∥ a == a ∥₀
    _π·_ = strunc-rec-bi strunc λ x y → ∣ x · y ∣₀
    
    πrefl : {A : Type ℓ} {a : A} → ∥ a == a ∥₀
    πrefl = ∣ refl _ ∣₀
  
    π·lunit : {A : Type ℓ} {a : A} → (p : ∥ a == a ∥₀) → πrefl π· p == p
    π·lunit {a = a} = strunc-ind-prop
      (λ _ → strunc-eq-prop)
      (λ a → ap ∣_∣₀ (inv (·-lunit a)))
  
    π·runit : {A : Type ℓ} {a : A} → (p : ∥ a == a ∥₀) → p π· πrefl == p
    π·runit {a = a} = strunc-ind-prop
      (λ _ → strunc-eq-prop)
      (λ a → ap ∣_∣₀ (inv (·-runit a)))
  
    π·assoc : {A : Type ℓ} {a : A} (x y z : ∥ a == a ∥₀) → (x π· (y π· z)) == (x π· y π· z)
    π·assoc = strunc-ind-tri-prop
      (λ _ _ _ → strunc-eq-prop)
      (λ x y z → ap ∣_∣₀ (inv (·-assoc x y z)))
  
    πinv : {A : Type ℓ} {a : A} → ∥ a == a ∥₀ → ∥ a == a ∥₀
    πinv = strunc-rec strunc λ x → ∣ inv x ∣₀
  
    π·linv : {A : Type ℓ} {a : A} → (p : ∥ a == a ∥₀) → p π· (πinv p) == πrefl
    π·linv = strunc-ind-prop (λ _ → strunc-eq-prop) λ a → ap ∣_∣₀ (·-rinv a)
  
    π·rinv : {A : Type ℓ} {a : A} → (p : ∥ a == a ∥₀) → (πinv p) π· p == πrefl
    π·rinv = strunc-ind-prop (λ _ → strunc-eq-prop) λ a → ap ∣_∣₀ (·-linv a)
  open PathStructure public

  -- Fundamental group
  π₁ : (A : Type ℓ) → (a : A) → Type ℓ
  π₁ A a = ∥ a == a ∥₀

  π₁-st : (A : Type ℓ) → (a : A) → GroupStructure ∥ a == a ∥₀
  π₁-st A a = group-structure strunc (_π·_) πrefl π·lunit π·runit π·assoc πinv π·linv π·rinv
  
  
