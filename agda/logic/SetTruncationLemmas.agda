{-# OPTIONS --without-K #-}

open import Base
open import Equality
open import logic.Propositions
open import logic.Sets
open import logic.HLevels
open import equivalence.EquivalenceSet
open import logic.SetTruncation

module logic.SetTruncationLemmas where

  strunc-rec-bi : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : Type ℓⱼ} → isSet P → (A → A → P) → ∥ A ∥₀ → ∥ A ∥₀ → P
  strunc-rec-bi prop op = strunc-rec (piSet λ a → prop) λ x → strunc-rec prop λ y → op x y

  strunc-ind-prop : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : ∥ A ∥₀ → Type ℓⱼ} → ((a : ∥ A ∥₀) → isProp (B a))
                  → (g : (a : A) → B ∣ a ∣₀) → (a : ∥ A ∥₀) → B a
  strunc-ind-prop α = strunc-ind (λ a → propIsSet (α a))


  strunc-ind-tri : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : ∥ A ∥₀ → ∥ A ∥₀ → ∥ A ∥₀ → Type ℓⱼ}
                 → ((x y z : ∥ A ∥₀) → isSet (B x y z))
                 → (g : (x y z : A) → B ∣ x ∣₀ ∣ y ∣₀ ∣ z ∣₀)
                 → (x y z : ∥ A ∥₀) → B x y z
  strunc-ind-tri {B = B} α g = strunc-ind (λ a → piSet λ b → piSet λ c → α a b c)
                               (λ x → strunc-ind (λ a → piSet λ b → α ∣ x ∣₀ a b)
                                 (λ y → strunc-ind (λ a → α ∣ x ∣₀ ∣ y ∣₀ a)
                                   (λ z → g x y z)))

  strunc-ind-tri-prop : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : ∥ A ∥₀ → ∥ A ∥₀ → ∥ A ∥₀ → Type ℓⱼ}
                      → ((x y z : ∥ A ∥₀) → isProp (B x y z))
                      → (g : (x y z : A) → B ∣ x ∣₀ ∣ y ∣₀ ∣ z ∣₀)
                      → (x y z : ∥ A ∥₀) → B x y z
  strunc-ind-tri-prop α = strunc-ind-tri λ x y z → propIsSet (α x y z)

  strunc-eq : ∀{ℓ} {A : Type ℓ} → {a b : A} → (p : a == b) → ∣ a ∣₀ == ∣ b ∣₀
  strunc-eq (refl a) = refl ∣ a ∣₀
  
  strunc-eq-prop : ∀{ℓ} {A : Type ℓ} → {a b : ∥ A ∥₀} → isProp (a == b)
  strunc-eq-prop {a = a} {b = b} = strunc a b

  
