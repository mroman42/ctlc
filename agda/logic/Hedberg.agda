{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality
open import Axioms
open import logic.Relation
open import logic.Propositions
open import logic.Sets

module logic.Hedberg where

  -- A set is a type satisfiying axiom K
  axiomKisSet : ∀{ℓ}  (A : Type ℓ) → ((a : A) → (p : a == a) → p == refl a) → isSet A
  axiomKisSet A k x _ p (refl _) = k x p
  
  -- A reflexive relation on X implies that it is a set
  reflRelIsSet : ∀{ℓ}  (A : Type ℓ) (r : Rel A) →
    ((x y : A) → R {{r}} x y → x == y) →
    (ρ : (a : A) → R {{r}} a a) →
    isSet A
  reflRelIsSet A r f ρ x y p q = {!!}
    where
      lemma : {a : A} (p : a == a) →
        p == (f a a (ρ a)) · inv (f a a (ρ a))
      lemma p = {!!}

      lemma2 : {a : A} (p : a == a) → (o : R {{r}} a a) →
        transport {!!} p (f a a o) == f a a o
      lemma2 = {!!}
        
      
  -- Hedberg's theorem
  lemDoubleNeg : ∀{ℓ}  (A : Type ℓ) → (A + ¬ A) → (¬ (¬ A) → A)
  lemDoubleNeg A (inl x) _ = x
  lemDoubleNeg A (inr f) n = exfalso (n f)

  hedberg : ∀{ℓ}  (A : Type ℓ) → ((a b : A) → (a == b) + ¬ (a == b)) → isSet A
  hedberg A f = reflRelIsSet A (record { R = λ a b → ¬ (¬ (a == b)) ; Rprop = isPropNeg }) doubleNegEq {!!}
    where
      doubleNegEq : (a b : A) → ¬ (¬ (a == b)) → (a == b)
      doubleNegEq a b = lemDoubleNeg (a == b) (f a b)

      isPropNeg : (a b : A) → isProp (¬ (¬ (a == b)))
      isPropNeg a b x y = fext x y λ u → exfalso (y u)
