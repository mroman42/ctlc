{-# OPTIONS --rewriting #-}

module Dyadics where

open import Integers renaming
  ( norm to normᶻ
  )
  public




-- Definition
odd : ℕ → Bool
odd zeroⁿ = false
odd (succ n) = ~ (odd n)

norm : ℕ → ℕ → ℕ → Prop
norm a b c = (c ≡≡ 0) ∨ (odd a ⊕ odd b ≡≡ true)

data Q2 : Set where
  q2 : (a b c : ℕ) → Prf (norm a b c) → Q2



-- Normalization
oddDec : (n : ℕ) → (odd n ≡ true) ⊎ (odd n ≡ false)
oddDec zeroⁿ = inr refl
oddDec (succ n) with (oddDec n)
oddDec (succ n) | inl x rewrite x = inr refl
oddDec (succ n) | inr x rewrite x = inl refl

half : (n : ℕ) → odd n ≡ false → ℕ
half zeroⁿ p = zeroⁿ
half (succ zeroⁿ) ()
half (succ (succ n)) p = succ (half n p)

half2 : (a b : ℕ) → odd a ⊕ odd b ≡ false → ℕ × ℕ
half2 zeroⁿ b p = zeroⁿ , half b p
half2 (succ zeroⁿ) zeroⁿ ()
half2 (succ zeroⁿ) (succ b) p = half2 zeroⁿ b p
half2 (succ (succ a)) b p with (half2 a b p)
half2 (succ (succ a)) b p | n , m = succ n , m


mkq2 : ℕ → ℕ → ℕ → Q2
mkq2 a b zeroⁿ = q2 a b zeroⁿ ∣ inl refl ∣
mkq2 a b (succ c) with (oddDec a) | (oddDec b)
mkq2 a b (succ c) | inl x | inl y = {!!}
mkq2 a b (succ c) | inr x | inr y = {!!}
mkq2 a b (succ c) | inl x | inr y = {!!}
mkq2 a b (succ c) | inr x | inl y = {!!}

