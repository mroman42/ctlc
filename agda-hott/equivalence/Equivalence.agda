{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality
open import Composition
open import Homotopies
open import logic.Contractible
open import logic.Fibers

module equivalence.Equivalence where

  module DefinitionOfEquivalence {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where
    -- Contractible maps. A map is contractible if the fiber in any
    -- point is contractible, that is, each element has a unique
    -- preimage.
    isContrMap : (f : A → B) → Type (ℓᵢ ⊔ ℓⱼ)
    isContrMap f = (b : B) → isContr (fib f b)
  
    -- There exists an equivalence between two types if there exists a
    -- contractible function between them.
    isEquiv : (f : A → B) → Type (ℓᵢ ⊔ ℓⱼ)
    isEquiv = isContrMap
  open DefinitionOfEquivalence public
  
  -- Equivalence of types.
  _≃_ : ∀{ℓᵢ ℓⱼ}  (A : Type ℓᵢ) (B : Type ℓⱼ) → Type (ℓᵢ ⊔ ℓⱼ)
  A ≃ B = Σ (A → B) isEquiv


  module EquivalenceMaps {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where
    -- Maps of an equivalence
    lemap : A ≃ B → (A → B)
    lemap = fst
  
    remap : A ≃ B → (B → A)
    remap (f , contrf) b = fst (fst (contrf b))
  
    -- The maps of an equivalence are inverses in particular
    lrmap-inverse : (eq : A ≃ B) → {b : B} → (lemap eq) ((remap eq) b) == b
    lrmap-inverse (f , eqf) {b} = fib-eq (fst (eqf b))
  
    rlmap-inverse : (eq : A ≃ B) → {a : A} → (remap eq) ((lemap eq) a) == a
    rlmap-inverse (f , eqf) {a} = ap fst ((snd (eqf (f a))) fib-image)

    lrmap-inverse-h : (eq : A ≃ B) → ((lemap eq) ∘ (remap eq)) ∼ id
    lrmap-inverse-h eq = λ x → lrmap-inverse eq {x}

    rlmap-inverse-h : (eq : A ≃ B) → ((remap eq) ∘ (lemap eq)) ∼ id
    rlmap-inverse-h eq = λ x → rlmap-inverse eq {x}
  open EquivalenceMaps public

  
