{-# OPTIONS --without-K #-}

open import Base
open import Equality
open import logic.Contractible
open import equivalence.Equivalence

module equality.CartesianProduct {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

  prodComponentwise : {x y : A × B} → (x == y) → ((fst x == fst y) × (snd x == snd y))
  prodComponentwise (refl a) = refl (fst a) , refl (snd a)

  prodByComponents : {x y : A × B} → ((fst x == fst y) × (snd x == snd y)) → (x == y)
  prodByComponents {x = a , b} (refl .a , refl .b) = refl (a , b)

  prodCompInverse : {x y : A × B} (b : ((fst x == fst y) × (snd x == snd y))) →
                    prodComponentwise (prodByComponents b) == b
  prodCompInverse {x} (refl .(fst x) , refl .(snd x)) = refl (refl (fst x) , refl (snd x))

  prodByCompInverse : {x y : A × B} (b : x == y) →
                    prodByComponents (prodComponentwise b) == b
  prodByCompInverse (refl a) = refl (refl a)

  -- prodEquality : {x y : A × B} → (x == y) ≃ ((fst x == fst y) × (snd x == snd y))
  -- prodEquality {x} {y} = prodComponentwise , λ b → (prodByComponents b , prodCompInverse b) , λ α → {!!}
  --   where
  --     lemma : {b : ((fst x == fst y) × (snd x == snd y))} (α : fib prodComponentwise b) →
  --       α == (prodByComponents b , prodCompInverse b)
  --     lemma (g , ginv) = {!!}
