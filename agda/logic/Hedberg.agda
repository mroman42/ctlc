{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality
open import equality.FunctionExtensionality
open import logic.Relation
open import logic.Propositions
open import logic.Sets

module logic.Hedberg {ℓ} where

  -- A set is a type satisfiying axiom K
  axiomKisSet : (A : Type ℓ) → ((a : A) → (p : a == a) → p == refl a) → isSet A
  axiomKisSet A k x _ p (refl _) = k x p
  
  -- A reflexive relation on X implying identity proves that X is a
  -- set.
  reflRelIsSet :  (A : Type ℓ) (r : Rel A) →
    ((x y : A) → R {{r}} x y → x == y) →
    (ρ : (a : A) → R {{r}} a a) →
    isSet A
  reflRelIsSet A r f ρ x .x p (refl .x) = lemma p
    where
      lemma2 : {a : A} (p : a == a) → (o : R {{r}} a a) →
        transport (λ x → a == x) p (f a a o) == f a a (transport (R {{r}} a) p o)
      lemma2 {a} p = funext-transport-l p (f a a) (f a a) (apd (f a) p)

      lemma3 : {a : A} (p : a == a) →
        (f a a (ρ a)) · p == (f a a (ρ a))
      lemma3 {a} p = inv (transport-concat-r p _) · lemma2 p (ρ a) ·
                     ap (f a a) (Rprop {{r}} a a _ (ρ a))

      lemma : {a : A} (p : a == a) → p == refl a
      lemma {a} p = ·-cancellation ((f a a (ρ a))) p (lemma3 p)


  -- Hedberg's theorem
  lemDoubleNeg : (A : Type ℓ) → (A + ¬ A) → (¬ (¬ A) → A)
  lemDoubleNeg A (inl x) _ = x
  lemDoubleNeg A (inr f) n = exfalso (n f)

  hedberg : {A : Type ℓ} → ((a b : A) → (a == b) + ¬ (a == b)) → isSet A
  hedberg {A} f = reflRelIsSet A
                (record { R = λ a b → ¬ (¬ (a == b)) ; Rprop = isPropNeg })
                doubleNegEq (λ a z → z (refl a))
    where
      doubleNegEq : (a b : A) → ¬ (¬ (a == b)) → (a == b)
      doubleNegEq a b = lemDoubleNeg (a == b) (f a b)

      isPropNeg : (a b : A) → isProp (¬ (¬ (a == b)))
      isPropNeg a b x y = funext λ u → exfalso (x u)
