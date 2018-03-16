{-# OPTIONS --rewriting #-}

open import Base renaming (_+_ to _+ₒ_)
open import Bool
open import Prop
open import Equality
open import naturals.Naturals
open import integers.Definition
open import integers.Successor
open import integers.Addition
open import integers.Multiplication


module integers.Even where

  -- Even numbers
  even : ℤ → Bool
  even zero = tt
  even (pos n) = ~ (evenⁿ n)
  even (neg n) = ~ (evenⁿ n)



  even-minus : ∀ n → even (- n) ≡ even n
  even-minus zero = refl
  even-minus (pos x) = refl
  even-minus (neg x) = refl
  {-# REWRITE even-minus #-}

  even-succsucc : ∀ n → even (succ (succ n)) ≡ even n
  even-succsucc zero = refl
  even-succsucc (pos x) = refl
  even-succsucc (neg zeroⁿ) = refl
  even-succsucc (neg (succⁿ zeroⁿ)) = refl
  even-succsucc (neg (succⁿ (succⁿ x))) = refl
  {-# REWRITE even-succsucc #-}

  even-succ : ∀ n → even (succ n) ≡ ~ (even n)
  even-succ zero = refl
  even-succ (pos zeroⁿ) = refl
  even-succ (pos (succⁿ zeroⁿ)) = refl
  even-succ (pos (succⁿ (succⁿ x))) = even-succ (pos x)
  even-succ (neg zeroⁿ) = refl
  even-succ (neg (succⁿ zeroⁿ)) = refl
  even-succ (neg (succⁿ (succⁿ x))) = even-succ (pos x)
  {-# REWRITE even-succ #-}


  even-pred : ∀ n → even (pred n) ≡ ~ (even n)
  even-pred zero = refl
  even-pred (pos zeroⁿ) = refl
  even-pred (pos (succⁿ x)) = refl
  even-pred (neg x) = refl
  {-# REWRITE even-pred #-}

  even-plus : ∀ a b → even (a + b) ≡ even a +ᵇ even b
  even-plus zero b = refl
  even-plus (pos zeroⁿ) b = refl
  even-plus (pos (succⁿ x)) b = ap ~ (even-plus (pos x) b)
  even-plus (neg zeroⁿ) b = refl
  even-plus (neg (succⁿ x)) b = ap ~ (even-plus (neg x) b)
  {-# REWRITE even-plus #-}

  even-plus-succ : ∀ n m → even (pos (n +ⁿ m)) ≡ ~ (even (pos n) +ᵇ even (pos m))
  even-plus-succ n m = ap ~ (even-plus (pos n) (pos m))
  -- {-# REWRITE even-plus-succ #-}

  even-mult : ∀ a b → even (a * b) ≡ even a *ᵇ even b
  even-mult zero b = refl
  even-mult (pos zeroⁿ) b = refl
  even-mult (pos (succⁿ x)) zero = refl
  even-mult (pos (succⁿ x)) (pos zeroⁿ) = refl
  even-mult (pos (succⁿ x)) (pos (succⁿ y)) = refl
  even-mult (pos (succⁿ x)) (neg zeroⁿ) = refl
  even-mult (pos (succⁿ x)) (neg (succⁿ y)) = refl
  even-mult (neg x) zero = refl
  even-mult (neg zeroⁿ) (pos y) = refl
  even-mult (neg (succⁿ x)) (pos zeroⁿ) = refl
  even-mult (neg (succⁿ x)) (pos (succⁿ y)) = refl
  even-mult (neg x) (neg zeroⁿ) = refl
  even-mult (neg zeroⁿ) (neg (succⁿ y)) = refl
  even-mult (neg (succⁿ x)) (neg (succⁿ y)) = refl
  {-# REWRITE even-mult #-}




  -- iseven-dec : ∀ z → (iseven z) +ₒ ¬ (iseven z)
  -- iseven-dec zero = inl ?
  -- iseven-dec (pos zeroⁿ) = inr ?
  -- iseven-dec (pos (succⁿ zeroⁿ)) = inl ?
  -- iseven-dec (pos (succⁿ (succⁿ x))) = iseven-dec (pos x)
  -- iseven-dec (neg zeroⁿ) = inr (λ ())
  -- iseven-dec (neg (succⁿ zeroⁿ)) = inl **
  -- iseven-dec (neg (succⁿ (succⁿ x))) = iseven-dec (neg x)

  Even : ℤ → Prop
  Even z = even z ≡≡ tt

  Odd : ℤ → Prop
  Odd n = even n ≡≡ ff

  Norm : ℤ → ℕ → Prop
  Norm z n = (Odd z) ∨ (n ≡≡ 0)

  Norm-succ : (z : ℤ) → (n : ℕ) → Prf (Norm z (succⁿ n)) → Prf (Norm z n)
  Norm-succ z n p with (even z)??
  Norm-succ z n p | inl x rewrite x = exfalsoₚ (trec {P = ⊥ₚ} ((λ { (inl ()) ; (inr ()) })) p)
  Norm-succ z n p | inr x = ∣ inl x ∣

  -- Norm-mult : (z z' : ℤ) → (n n' : ℕ)
  --   → Prf (Norm z n)
  --   → Prf (Norm z' n')
  --   → Prf (Norm (z * z') (n +ⁿ n'))
  -- Norm-mult z z' zeroⁿ zeroⁿ p q = ∣ inr refl ∣
  -- Norm-mult z z' zeroⁿ (succⁿ n') p q = {!!}
  -- Norm-mult z z' (succⁿ n) n' p q = {!!}

  half : ∀ z → Prf (Even z) → ℤ
  half zero p = zero
  half (pos zeroⁿ) ()
  half (pos (succⁿ zeroⁿ)) p = pos zeroⁿ
  half (pos (succⁿ (succⁿ x))) p = succ (half (pos x) p)
  half (neg zeroⁿ) ()
  half (neg (succⁿ zeroⁿ)) p = neg zeroⁿ
  half (neg (succⁿ (succⁿ x))) p = pred (half (neg x) p)

  exp2 : ℕ → ℤ
  exp2 zeroⁿ = pos zeroⁿ
  exp2 (succⁿ n) = pos (succⁿ zeroⁿ) * exp2 n

  

  -- normalized : ℤ → ℕ → Set
  -- normalized mnt zeroⁿ = ⊤
  -- normalized mnt (succⁿ exp) = ¬ (iseven mnt)

  -- normalized-dec : (z : ℤ) → (n : ℕ) → (normalized z n) +ₒ ¬ (normalized z n)
  -- normalized-dec z zeroⁿ = inl **
  -- normalized-dec z (succⁿ n) with (iseven-dec z)
  -- normalized-dec z (succⁿ n) | inl x = inr (λ f → f x)
  -- normalized-dec z (succⁿ n) | inr x = inl x
