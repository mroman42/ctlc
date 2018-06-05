{-# OPTIONS --without-K #-}

-- Agda-hott library.
-- Author: Mario Román

-- CartesianProduct.  Equality in the particular case of cartesian
-- products.

open import Base
open import Equality
open import logic.Contractible
open import equivalence.Equivalence

module equality.CartesianProduct {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ} where

  -- In a pair, the equality of the two components of the pairs is
  -- equivalent to equality of the two pairs.
  prodComponentwise : {x y : A × B} → (x == y) → ((fst x == fst y) × (snd x == snd y))
  prodComponentwise (refl a) = refl (fst a) , refl (snd a)

  prodByComponents : {x y : A × B} → ((fst x == fst y) × (snd x == snd y)) → (x == y)
  prodByComponents {x = a , b} (refl .a , refl .b) = refl (a , b)


  -- This is in fact an equivalence.
  prodCompInverse : {x y : A × B} (b : ((fst x == fst y) × (snd x == snd y))) →
                    prodComponentwise (prodByComponents b) == b
  prodCompInverse {x} (refl .(fst x) , refl .(snd x)) = refl (refl (fst x) , refl (snd x))

  prodByCompInverse : {x y : A × B} (b : x == y) →
                    prodByComponents (prodComponentwise b) == b
  prodByCompInverse (refl a) = refl (refl a)
