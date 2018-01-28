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
  
  prodEquality : {x y : A × B} → (x == y) ≃ ((fst x == fst y) × (snd x == snd y))
  prodEquality = prodComponentwise , {!!}
