{-# OPTIONS --without-K #-}

open import Base
open import Equality
open import EquationalReasoning
open import Homotopies
open import Composition
open import logic.Contractible
open import logic.Propositions
open import equality.Sigma
open import equivalence.Equivalence
open import equivalence.Halfadjoints

module equivalence.Quasiinverses {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where
  
  -- Definitions for quasiinverses, left-inverses, right-inverses and
  -- biinverses.
  qinv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
  qinv f = Σ (B → A) (λ g → ((f ∘ g) ∼ id) × ((g ∘ f) ∼ id))

  -- record qinv (f : A → B) : Type (ℓᵢ ⊔ ℓⱼ) where
  --   field
  --     g : B → A
  --     η : (g ∘ f) ∼ id
  --     ε : (f ∘ g) ∼ id

  linv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
  linv f = Σ (B → A) (λ g → (g ∘ f) ∼ id)

  rinv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
  rinv f = Σ (B → A) λ g → (f ∘ g) ∼ id

  biinv : (A → B) → Type (ℓᵢ ⊔ ℓⱼ)
  biinv f = linv f × rinv f

  qinv-biinv : (f : A → B) → qinv f → biinv f
  qinv-biinv f (g , (u1 , u2)) = (g , u2) , (g , u1)

  biinv-qinv : (f : A → B) → biinv f → qinv f
  biinv-qinv f ((h , α) , (g , β)) = g , (β , δ)
    where
      γ1 : g ∼ ((h ∘ f) ∘ g)
      γ1 = rcomp-∼ g (h-simm (h ∘ f) id α)
      
      γ2 : ((h ∘ f) ∘ g) ∼ (h ∘ (f ∘ g))
      γ2 x = refl (h (f (g x)))
       
      γ : g ∼ h
      γ = γ1 ● (γ2 ● (lcomp-∼ h β))
       
      δ : (g ∘ f) ∼ id
      δ = (rcomp-∼ f γ) ● α

  -- TODO: Propositions
  -- linvIsProp : (f : A → B) → isProp (linv f)
  -- linvIsProp f = {!!}

  equiv-biinv : (f : A → B) → isContrMap f → biinv f
  equiv-biinv f contrf = (remap eq , rlmap-inverse-h eq) , (remap eq , lrmap-inverse-h eq)
    where
      eq : A ≃ B
      eq = f , contrf

  qinv-ishae : {f : A → B} → qinv f → ishae f
  qinv-ishae {f} (g , (ε , η)) = record {
      g = g ;
      η = η ;
      ε = λ b → inv (ε (f (g b))) · ap f (η (g b)) · ε b ;
      τ = τ
    }
    where
      lemma1 : (a : A) → ap f (η (g (f a))) · ε (f a) == ε (f (g (f a))) · ap f (η a)
      lemma1 a = 
        begin
          ap f (η ((g ∘ f) a)) · ε (f a)       ==⟨ ap (λ u → ap f u · ε (f a)) (h-naturality-id η) ⟩
          ap f (ap (g ∘ f) (η a)) · ε (f a)    ==⟨ ap (_· ε (f a)) (ap-comp (g ∘ f) f (η a)) ⟩
          ap (f ∘ (g ∘ f)) (η a) · ε (f a)     ==⟨ inv (h-naturality (λ x → ε (f x)) (η a)) ⟩
          ε (f (g (f a))) · ap f (η a)
        ∎
      
      τ : (a : A) → ap f (η a) == (inv (ε (f (g (f a)))) · ap f (η (g (f a))) · ε (f a))
      τ a = 
        begin
          ap f (η a)                                               ==⟨ ap (_· ap f (η a))
                                                                       (inv (·-linv (ε (f (g (f a)))))) ⟩
          inv (ε (f (g (f a)))) · ε (f (g (f a))) · ap f (η a)     ==⟨ ·-assoc (inv (ε (f (g (f a))))) _
                                                                       (ap f (η a)) ⟩
          inv (ε (f (g (f a)))) · (ε (f (g (f a))) · ap f (η a))   ==⟨ ap (inv (ε (f (g (f a)))) ·_)
                                                                       (inv (lemma1 a)) ⟩
          inv (ε (f (g (f a)))) · (ap f (η (g (f a))) · ε (f a))   ==⟨ inv (·-assoc
                                                                       (inv (ε (f (g (f a))))) _ (ε (f a))) ⟩
          inv (ε (f (g (f a)))) · ap f (η (g (f a))) · ε (f a)
        ∎

  qinv-≃ : (f : A → B) → qinv f → A ≃ B
  qinv-≃ f = ishae-≃ ∘ qinv-ishae

  ≃-qinv : A ≃ B → Σ (A → B) qinv
  ≃-qinv eq = lemap eq , (remap eq , (lrmap-inverse-h eq , rlmap-inverse-h eq))

  ishae-qinv : {f : A → B} → ishae f → qinv f
  ishae-qinv {f} (hae g η ε τ) = g , (ε , η)

  -- qinv-equiv : (f : A → B) → qinv f → isContrMap f
  -- qinv-equiv f (g , (α , β)) b = ((g b) , α b) , {!!}
  --   where
  --     uniq : (x : fib f b) → (g b , α b) == x
  --     uniq (a , p) = Σ-bycomponents ((ap g (inv p) · β a) , {!!})

  -- biinv-equiv : (f : A → B) → biinv f → isContrMap f
  -- biinv-equiv f ((gl , hgl) , (gr , hgr)) = λ b → {!!}

