{-# OPTIONS --without-K #-}

-- Agda-hott library.
-- Author: Mario Román

-- Univalence.  Voevodsky's univalence axiom is postulated. It induces
-- an equality between any two equivalent types. Some β and η rules
-- are provided.

open import Base
open import Equality
open import EquationalReasoning
open import equality.Sigma
open import logic.Contractible
open import equivalence.Equivalence
open import equivalence.EquivalenceProp
open import equivalence.Quasiinverses
open import equivalence.EquivalenceComposition

module equality.Univalence where

  -- Voevodsky's Univalence Axiom.
  module UnivalenceAxiom {ℓ} {A B : Type ℓ} where
    idtoeqv : A == B → A ≃ B
    idtoeqv p = qinv-≃
      (transport (λ x → x) p)
      (transport (λ x → x) (inv p) , (transport-inv-l p , transport-inv-r p))

    -- The Univalence axiom induces an equivalence between equalities
    -- and equivalences.
    postulate axiomUnivalence : isEquiv idtoeqv
    eqvUnivalence : (A == B) ≃ (A ≃ B)
    eqvUnivalence = idtoeqv , axiomUnivalence

    -- Introduction rule for equalities.
    ua : A ≃ B → A == B
    ua = remap eqvUnivalence

    -- Computation rules
    ua-β : (eqv : A ≃ B) → idtoeqv (ua eqv) == eqv
    ua-β eqv = lrmap-inverse eqvUnivalence

    ua-η : (p : A == B) → ua (idtoeqv p) == p
    ua-η p = rlmap-inverse eqvUnivalence
  open UnivalenceAxiom public

  
  module UnivalenceLemmas {ℓ} where
    -- The identity equivalence creates the trivial path.
    ua-id : {A : Type ℓ} → ua idEqv == refl A
    ua-id {A} = 
      begin
        ua idEqv              ==⟨ ap ua (sameEqv (refl id)) ⟩
        ua (idtoeqv (refl A)) ==⟨ ua-η (refl A) ⟩
        refl A
      ∎

    -- The composition of equivalences is preserved into composition
    -- of equalities.
    ua-comp : {A B C : Type ℓ} → (α : A ≃ B) → (β : B ≃ C) → ua (compEqv α β) == ua α · ua β
    ua-comp α β = 
      begin
        ua (compEqv α β)                               ==⟨ ap (λ x → ua (compEqv x β)) (inv (ua-β α)) ⟩
        ua (compEqv (idtoeqv (ua α)) β)                ==⟨ ap (λ x → ua (compEqv (idtoeqv (ua α)) x))
                                                           (inv (ua-β β)) ⟩
        ua (compEqv (idtoeqv (ua α)) (idtoeqv (ua β))) ==⟨ ap ua lemma ⟩
        ua (idtoeqv (ua α · ua β))                     ==⟨ ua-η (ua α · ua β) ⟩
        ua α · ua β
      ∎
      where
        lemma : compEqv (idtoeqv (ua α)) (idtoeqv (ua β)) == idtoeqv (ua α · ua β)
        lemma = sameEqv (
          begin
            fst (idtoeqv (ua β)) ∘ fst (idtoeqv (ua α))                 ==⟨ refl _ ⟩
            (transport (λ x → x) (ua β)) ∘ (transport (λ x → x) (ua α)) ==⟨ transport-comp (ua α) (ua β) ⟩
            transport (λ x → x) (ua α · ua β)                           ==⟨ refl _ ⟩
            fst (idtoeqv (ua α · ua β))
          ∎)

    -- Inverses are preserved.
    ua-inv-r : {A B : Type ℓ} → (α : A ≃ B) → ua α · ua (invEqv α) == refl A
    ua-inv-r α = 
      begin
        ua α · ua (invEqv α)      ==⟨ inv (ua-comp α (invEqv α)) ⟩
        ua (compEqv α (invEqv α)) ==⟨ ap ua (compEqv-inv α) ⟩
        ua idEqv                  ==⟨ ua-id ⟩
        refl _
      ∎

    ua-inv : {A B : Type ℓ} → (α : A ≃ B) → ua (invEqv α) == inv (ua α)
    ua-inv α = 
      begin
        ua (invEqv α)                       ==⟨ ap (_· ua (invEqv α)) (inv (·-linv (ua α))) ⟩
        inv (ua α) · ua α · ua (invEqv α)   ==⟨ ·-assoc (inv (ua α)) _ _ ⟩
        inv (ua α) · (ua α · ua (invEqv α)) ==⟨ ap (inv (ua α) ·_) (ua-inv-r α) ⟩
        inv (ua α) · refl _                 ==⟨ inv (·-runit (inv ((ua α)))) ⟩
        inv (ua α)
      ∎
  open UnivalenceLemmas public
