open import Relation.Binary.PropositionalEquality
open import Data.Integer hiding (_+_)
open import Agda.Builtin.Int
open import Data.Integer.Properties
open import Data.Integer.Divisibility
open import Data.Nat renaming (_+_ to _+ⁿ_; _*_ to _*ⁿ_)
open import Data.Product
open import Data.Sum

module Dyadics where

  Normalized : (z : ℤ) → (n : ℕ) → Set
  Normalized z n = (pos 2 ∣ z) ⊎ (n ≡ 0)

  data Dyadic : Set where
    dyadic : (z : ℤ) → (n : ℕ) → Normalized z n → Dyadic

  _+_ : Dyadic → Dyadic → Dyadic
  dyadic z zero x + dyadic z' n' x' = dyadic (z * z') 0 (inj₂ refl)
  dyadic z (ℕ.suc n) x + dyadic z' n' x' = dyadic {!!} {!!} {!!}
  
