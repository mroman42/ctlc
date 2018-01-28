{-# OPTIONS --without-K #-}

open import Base
open import Equality
open import logic.Contractible
open import equivalence.Equivalence

module equality.CartesianProduct {ℓ} {A B : Type ℓ} where

  prodComponentwise : {x y : A × B} → (x == y) → ((fst x == fst y) × (snd x == snd y))
  prodComponentwise (refl a) = refl (fst a) , refl (snd a)

  prodByComponents : {x y : A × B} → ((fst x == fst y) × (snd x == snd y)) → (x == y)
  prodByComponents {x = a , b} (refl .a , refl .b) = refl (a , b)

  prodCompInverse : {x y : A × B} (b : ((fst x == fst y) × (snd x == snd y))) →
                    prodComponentwise (prodByComponents b) == b
  prodCompInverse {x} (refl .(fst x) , refl .(snd x)) = refl (refl (fst x) , refl (snd x))

  -- prodEquality : {x y : A × B} → (x == y) ≃ ((fst x == fst y) × (snd x == snd y))
  -- prodEquality {x} {y} = prodComponentwise , λ b → (prodByComponents b , prodCompInverse b) , λ α → {!!}
  --   where
  --     lemma : {b : ((fst x == fst y) × (snd x == snd y))} (α : fib prodComponentwise b) →
  --       α == (prodByComponents b , prodCompInverse b)
  --     lemma (g , ginv) = {!!}
