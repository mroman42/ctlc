{-# OPTIONS --rewriting #-}

module Integers where

open import Naturals renaming
 ( _+_ to _+ⁿ_
 ; _*_ to _*ⁿ_
 ; _≡?_ to _≡?ⁿ_
 ; +comm to +commⁿ
 ; zero to zeroⁿ
 )
 public



-- Definition
norm : ℕ → ℕ → Prop
norm n m = (n ≡≡ 0) ∨ (m ≡≡ 0)

non-norm : ∀ n m → Prf (norm (succ n) (succ m)) → ⊥
non-norm n m p = trec {P = ⊥ₚ} (λ { (inl ()) ; (inr ()) }) p


data ℤ : Set where
  int : (n m : ℕ) → Prf (norm n m) → ℤ

mkint : ℕ → ℕ → ℤ
mkint zeroⁿ m = int zeroⁿ m ∣ inl refl ∣
mkint (succ n) zeroⁿ = int (succ n) zeroⁿ ∣ inr refl ∣
mkint (succ n) (succ m) = mkint n m

mkint-idemp : (n m : ℕ) → (p : Prf (norm n m)) → int n m p ≡ mkint n m
mkint-idemp zeroⁿ m p = ap (λ q → int zeroⁿ m q) (isprop (norm zeroⁿ m) p ∣ inl refl ∣)
mkint-idemp (succ n) zeroⁿ p = ap (λ q → int (succ n) zeroⁿ q) (isprop (norm (succ n) zeroⁿ) p ∣ inr refl ∣)
mkint-idemp (succ n) (succ m) p with (non-norm n m p)
mkint-idemp (succ n) (succ m) p | ()



-- Decidable equality
infix 5 _≡?_
_≡?_ : ℤ → ℤ → Bool
int a b x ≡? int c d x₁ = ((a +ⁿ d) ≡?ⁿ (c +ⁿ b))

≡?mkint-mkint : ∀ a b c d → (mkint a b ≡? mkint c d) ≡ (a +ⁿ d ≡?ⁿ c +ⁿ b)
≡?mkint-mkint zeroⁿ b zeroⁿ d = refl
≡?mkint-mkint zeroⁿ b (succ c) zeroⁿ = refl
≡?mkint-mkint zeroⁿ b (succ c) (succ d) = ≡?mkint-mkint zeroⁿ b c d
≡?mkint-mkint (succ a) zeroⁿ zeroⁿ d = refl
≡?mkint-mkint (succ a) zeroⁿ (succ c) zeroⁿ = refl
≡?mkint-mkint (succ a) zeroⁿ (succ c) (succ d) = ≡?mkint-mkint (succ a) zeroⁿ c d
≡?mkint-mkint (succ a) (succ b) c d = ≡?mkint-mkint a b c d
{-# REWRITE ≡?mkint-mkint #-}

≡?mkint-l : (z : ℤ) (n m : ℕ) (p : Prf (norm n m)) → (z ≡? int n m p) ≡ (z ≡? mkint n m)
≡?mkint-l z n m p = ap (z ≡?_) (mkint-idemp n m p)
{-# REWRITE ≡?mkint-l #-}

≡?mkint-r : (z : ℤ) (n m : ℕ) (p : Prf (norm n m)) → (int n m p ≡? z) ≡ (mkint n m ≡? z)
≡?mkint-r z n m p = ap (_≡? z) (mkint-idemp n m p)
{-# REWRITE ≡?mkint-r #-}



-- Numbers
zero : ℤ
zero = mkint zeroⁿ zeroⁿ

one : ℤ
one = mkint (succ zeroⁿ) zeroⁿ



-- Addition
_+_ : ℤ → ℤ → ℤ
int a b p + int c d q = mkint (a +ⁿ c) (b +ⁿ d)

+comm : (a b : ℤ) → (a + b ≡? b + a) ≡ true
+comm (int n m x) (int n₁ m₁ x₁) = refl

+zero-l : ∀ a → (zero + a ≡? a) ≡ true
+zero-l (int n m x) = refl

-- +zero-r : ∀ a → (a + zero ≡? a) ≡ true
-- +zero-r (int n m x) = {!!}
