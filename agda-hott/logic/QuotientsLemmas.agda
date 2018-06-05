{-# OPTIONS --without-K #-}


-- Agda-hott library.
-- Author: Mario Román

-- QuotientLemmas.  Lemmas about quotient types.

open import Base
open import Equality
open import logic.Propositions
open import logic.Sets
open import logic.Quotients
open import equality.FunctionExtensionality
open import equality.Sigma
open import EquationalReasoning

module logic.QuotientsLemmas where

  Qrel-prod : ∀{ℓᵢ}{A : Type ℓᵢ} (r : QRel A) → QRel (A × A)
  Qrel-prod r = record { R = λ { (a , b) (c , d) → (R {{r}} a c) × (R {{r}} b d) }
                       ; Aset = isSet-prod (Aset {{r}}) (Aset {{r}})
                       ; Rprop = λ { (x , y) (z , w) → isProp-prod (Rprop {{r}} x z) (Rprop {{r}} y w)} }
