{-# OPTIONS --without-K #-}

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

  QRel-rec-bi : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {r : QRel A} {B : Type ℓⱼ} 
              → (f : A → A → B)
              → ({a b c d : A} → R {{r}} a c → R {{r}} b d → f a b == f c d)
              → A / r → A / r → B
  QRel-rec-bi {A = A} {r = r} {B = B} f α a b = g {!!}
    where
      g : (A × A) / (Qrel-prod r) → B
      g = QRel-rec (λ {(n , m) → f n m}) λ { (x1 , x2) (y1 , y2) o → α (fst o) (snd o) }
