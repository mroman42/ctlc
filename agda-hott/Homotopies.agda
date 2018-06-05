{-# OPTIONS --without-K #-}

-- Agda-hott library.
-- Author: Mario Román

-- Homotopies.  In a type-theoretical sense, a homotopy between two
-- functions is a family of equalities between their applications.

open import Agda.Primitive
open import Base
open import Equality
open import EquationalReasoning
open import Composition

module Homotopies where

  module Homotopy {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : A → Type ℓⱼ} where
    -- A homotopy is a natural isomorphism between two functions, we will write
    -- f ∼ g when (f x == g x) for all x.
    homotopy : (f g : ((x : A) → P x)) → Type (ℓᵢ ⊔ ℓⱼ)
    homotopy f g = (x : A) → f x == g x
  
    _∼_ : (f g : ((x : A) → P x)) → Type (ℓᵢ ⊔ ℓⱼ)
    f ∼ g = homotopy f g
  
  
    -- Homotopy is an equivalence relation
    h-refl : (f : (x : A) → P x) → f ∼ f
    h-refl f x = refl (f x)
  
    h-simm : (f g : (x : A) → P x) → f ∼ g → g ∼ f
    h-simm f g u x = inv (u x)
  
    h-comp : (f g h : (x : A) → P x) → f ∼ g → g ∼ h → f ∼ h
    h-comp f g h u v x = (u x)·(v x)

    _●_ : {f g h : (x : A) → P x} → f ∼ g → g ∼ h → f ∼ h
    α ● β = h-comp _ _ _ α β
    
  open Homotopy public

  -- Composition with homotopies
  module HomotopyComposition {ℓᵢ ℓⱼ ℓₖ} {A : Type ℓᵢ} {B : Type ℓⱼ} {C : Type ℓₖ} where
    hl-comp : (f g : A → B) → (j k : B → C) → f ∼ g → j ∼ k → (j ∘ f) ∼ (k ∘ g)
    hl-comp f g j k α β x = ap j (α x) · β (g x)
  
    rcomp-∼ : (f : A → B) → {j k : B → C} → j ∼ k → (j ∘ f) ∼ (k ∘ f)
    rcomp-∼ f β = hl-comp _ _ _ _ (h-refl f) β
  
    lcomp-∼ : {f g : A → B} → (j : B → C) → f ∼ g → (j ∘ f) ∼ (j ∘ g)
    lcomp-∼ j α = hl-comp _ _ _ _ α (h-refl j)
  open HomotopyComposition public

  -- Homotopy is natural, meaning that it satisfies the following
  -- square commutative diagram.
  module Naturality {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where
    h-naturality : {f g : A → B} (H : f ∼ g) → {x y : A} → (p : x == y)
                 → H x · ap g p == ap f p · H y
    h-naturality H (refl a) = inv (·-runit (H a))
  open Naturality public

  -- A particular case of naturality on the identity function.
  h-naturality-id : ∀{ℓ} {A : Type ℓ} {f : A → A} (H : f ∼ id) → {x : A}
                  → H (f x) == ap f (H x)
  h-naturality-id {f = f} H {x = x} =
    begin
      H (f x)                            ==⟨ ·-runit (H (f x)) ⟩
      H (f x) · (refl (f x))             ==⟨ ap (H (f x) ·_) (inv (·-rinv (H x))) ⟩
      H (f x) · (H x · inv (H x))        ==⟨ inv (·-assoc (H (f x)) _ (inv (H x))) ⟩
      H (f x) · H x · inv (H x)          ==⟨ ap (λ u → H (f x) · u · inv (H x)) (inv (ap-id _)) ⟩
      H (f x) · ap id (H x) · inv (H x)  ==⟨ ap (_· inv (H x)) (h-naturality H (H x)) ⟩
      ap f (H x) · H x · inv (H x)       ==⟨ ·-assoc (ap f (H x)) _ (inv (H x)) ⟩
      ap f (H x) · (H x · inv (H x))     ==⟨ ap (ap f (H x) ·_) (·-rinv (H x)) ⟩
      ap f (H x) · refl (f x)            ==⟨ inv (·-runit (ap f (H x))) ⟩
      ap f (H x)
    ∎
