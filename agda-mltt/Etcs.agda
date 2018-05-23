{-# OPTIONS --exact-split --without-K --type-in-type #-}

module Etcs where

open import Base
open import Prop
open import Booleans
open import Naturals


-- This proof has been adapted from Diaconescu's theorem in the
-- version by Altenkirch's notes on Homotopy type theory.

wellPointed : {A : Set} {B : A → Set} → {f g : (a : A) → B a}
  → ((x : A) → f x ≡ g x)
  ------------------------
  → f ≡ g
wellPointed = funext


postulate 
  AxiomOfChoice : {A : Set} {B : Set} {R : A → B → Set}
    → ((a : A) → (∃ b ∈ B , (R a b)))
    ------------------------------------------
    → (∃ g ∈ (A → B), ((a : A) → R a (g a)))
    

LawOfExcludedMiddle : {P : Set} → P ∨ ¬ P
LawOfExcludedMiddle {P} = Ex-elim
  (AxiomOfChoice λ { (Q , q) → Ex-elim q Ex-isProp λ { (u , v) → u ,, v  }})
  ∨-isProp λ { (f , α) → byCases f α }
  where
    A : Set
    A = Σ (Bool → Set) (λ Q → Ex Bool (λ b → Q b))

    R : A → Bool → Set
    R (P , _) b = P b

    U : Bool → Set
    U b = (b ≡ true) ∨ P
    V : Bool → Set
    V b = (b ≡ false) ∨ P
    Ua : A
    Ua = U , (true ,, rinl refl)
    Va : A
    Va = V , (false ,, rinl refl)

    module lemma (f : A → Bool) where
      eqf : (p : P) → f Ua ≡ f Va 
      eqf p = ap f (Σ-eq Ua Va (
        wellPointed λ
          { false → propext ∨-isProp ∨-isProp (λ _ → rinr p) (λ _ → rinr p)
          ; true  → propext ∨-isProp ∨-isProp (λ _ → rinr p) (λ _ → rinr p)
          }) (Ex-isProp _ _))
        
      refute : true ≡ false → P ∨ ¬ P
      refute ()
      byCases : (α : (x : A) → R x (f x)) → P ∨ ¬ P
      byCases α with f Ua ?? | f Va ??
      byCases α | inl x | inr y = rinr λ p → true≢false (inv x · (eqf p · y))
      byCases α | inl x | inl y = ∨-elim (α Va) ∨-isProp λ { (inl q) → refute (inv y · q) ; (inr p) → rinl p }
      byCases α | inr x | inl y = ∨-elim (α Ua) ∨-isProp λ { (inl q) → refute (inv q · x) ; (inr p) → rinl p }
      byCases α | inr x | inr y = ∨-elim (α Ua) ∨-isProp λ { (inl q) → refute (inv q · x) ; (inr p) → rinl p }
    open lemma public
