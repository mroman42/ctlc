{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality

module equality.Sigma {ℓᵢ ℓⱼ} {A : Type ℓᵢ} {P : A → Type ℓⱼ} where

  Σ-componentwise : {v w : Σ A P} → v == w → Σ (fst v == fst w) (λ p → (p ✶) (snd v) == snd w)
  Σ-componentwise {v} {.v} (refl .v) = refl (fst v) , refl (snd v)

  Σ-bycomponents : {v w : Σ A P} → Σ (fst v == fst w) (λ p → (p ✶) (snd v) == snd w) → v == w
  Σ-bycomponents {(a , f)} {(.a , .f)} (refl .a , refl .f) = refl (a , f)
