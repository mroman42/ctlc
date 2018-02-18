{-# OPTIONS --rewriting #-}

open import Base
open import Prop
open import Equality
open import naturals.Definition

module naturals.Successor where

  succ-inj-l : ∀ n m → Prf ((n ≡≡ m) ~> (succ n ≡≡ succ m))
  succ-inj-l n m p = ap succ p
  
  succ-inj-r : ∀ n m → Prf ((succ n ≡≡ succ m) ~> (n ≡≡ m))
  succ-inj-r n .n refl = refl
  
  succ-inj : ∀ n m → Prf ((succ n ≡≡ succ m) <~> (n ≡≡ m))
  succ-inj n m = succ-inj-r n m , succ-inj-l n m  
