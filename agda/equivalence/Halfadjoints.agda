{-# OPTIONS --without-K #-}

open import Base
open import Equality
open import Homotopies
open import Composition
open import logic.Contractible
open import logic.Propositions

module equivalence.Halfadjoints {ℓ} {A B : Type ℓ} where

  -- Half adjoint equivalence
  record ishae (f : A → B) : Type ℓ where
    field
      g : B → A
      η : (g ∘ f) ∼ id
      ε : (f ∘ g) ∼ id
      hae : (x : A) → ap f (η x) == ε (f x)
    
  -- Half adjoint equivalences give contractible fibers
  ishae-contr : (f : A → B) → ishae f → (y : B) → isContr (fib f y)
  ishae-contr f record { g = g ; η = η ; ε = ε ; hae = hae } y = ((g y) , (ε y)) , λ { (a , p) → {!!} }
