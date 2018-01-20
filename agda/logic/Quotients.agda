{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality
open import logic.Propositions
open import logic.Sets

module logic.Quotients where


  record QRel {ℓ} (A : Type ℓ) : Type (lsuc ℓ) where
    field
      R : A → A → Type ℓ
      Aset : isSet A
      Rprop : (a b : A) → isProp (R a b)
  open QRel {{...}} public
  
  private
    -- Higher inductive type
    data _!/_ {ℓ} (A : Type ℓ) (r : QRel A) : Type (lsuc ℓ) where
      ![_] : A → (A !/ r)

  _/_ : ∀{ℓ} (A : Type ℓ) (r : QRel A) → Type (lsuc ℓ)
  A / r = (A !/ r)
  

  [_] : ∀{ℓ} {A : Type ℓ} → A → {r : QRel A} → (A / r)
  [ a ] = ![ a ]

  -- Equalities induced by the relation
  postulate Req : ∀{ℓ} {A : Type ℓ} {r : QRel A}
                 → (a b : A) → R {{r}} a b → [ a ] {r} == [ b ]
                  
  -- Truncation as a set of the relation
  postulate Rtrunc : ∀{ℓ} {A : Type ℓ} {r : QRel A}
                    → isSet (A / r)
                     
  -- Recursion principle
  QRel-rec : ∀{ℓ} {A B : Type ℓ} {r : QRel A}
            → (f : A → B) → ((x y : A) → R {{r}} x y → f x == f y) → A / r → B
  QRel-rec f p ![ x ] = f x
