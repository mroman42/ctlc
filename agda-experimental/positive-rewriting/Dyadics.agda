{-# OPTIONS --rewriting #-}

module Dyadics where

open import Naturals renaming (_≡?_ to _≡?ⁿ_ ; from≡? to from≡?ⁿ)


Normalized : ℕ → ℕ → Set
Normalized n e = or (odd n) (iszero e) ≡ true


data Dyadic : Set where
  dyadic : (n e : ℕ) → Normalized n e → Dyadic

numerator : Dyadic → ℕ
numerator (dyadic n _ _) = n

exponent : Dyadic → ℕ
exponent (dyadic _ e _) = e


mkdyadic : ℕ → ℕ → Dyadic
mkdyadic n e with (odd n)??
mkdyadic n e | inl x = dyadic n e (ap (λ u → or u (iszero e)) x)
mkdyadic n e | inr x with (iszero e)??
mkdyadic n e | inr x | inl y = dyadic n e (ap (λ u → or (odd n) u) y)
mkdyadic n zero | inr x | inr ()
mkdyadic n (succ e) | inr x | inr y with (even-form n x)
mkdyadic n (succ e) | inr x | inr y | m , _ = mkdyadic m e


mkdyadic-sound : (n e : ℕ) → numerator (mkdyadic n e) * exp2 e ≡ n * exp2 (exponent (mkdyadic n e))
mkdyadic-sound n e with (odd n)??
mkdyadic-sound n e | inl x = refl
mkdyadic-sound n e | inr x with (iszero e)??
mkdyadic-sound n e | inr x | inl y = refl
mkdyadic-sound n zero | inr x | inr ()
mkdyadic-sound n (succ e) | inr x | inr y with (even-form n x)
mkdyadic-sound n (succ e) | inr x | inr y | m , p = 
  begin
    numerator (mkdyadic m e) * (exp2 e + (exp2 e + 0)) ≡⟨ {!!} ⟩
    (m + (m + 0)) * exp2 (exponent (mkdyadic m e)) ≡⟨ ap (λ u → u * exp2 (exponent (mkdyadic m e))) (inv eq) ⟩
    n * exp2 (exponent (mkdyadic m e))
  qed
  where
    eq : n ≡ m + (m + 0)
    eq = inv (from≡?ⁿ p)
