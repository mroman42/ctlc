{-# OPTIONS --rewriting #-}

open import Base hiding (_+_)
open import Equality
open import naturals.Naturals
open import integers.Integers 
open import Prop
open import Bool

module dyadics.Definition where

  data Dyadic : Set where
    dyadic : (z : ℤ) → (n : ℕ) → (p : Prf (Norm z n)) → Dyadic

  -- Negation
  - : Dyadic → Dyadic
  - (dyadic z n o) = dyadic (-ᶻ z) n o

  -- Dyadic equality
  drefl : {z : ℤ} {n : ℕ} {p q : Prf (Norm z n)} → dyadic z n p ≡ dyadic z n q
  drefl {z} {n} {p} {q} with (isprop (Norm z n) p q)
  drefl {z} {n} {p} {.p} | refl = refl

  half : Dyadic → Dyadic
  half (dyadic z zeroⁿ p) with (even z)??
  half (dyadic z zeroⁿ p) | inl q = dyadic (halfᶻ z q) zeroⁿ ∣ inr refl ∣
  half (dyadic z zeroⁿ p) | inr q = dyadic z (succⁿ zeroⁿ) ∣ inl q ∣
  half (dyadic z (succⁿ n) p) with (even z)??
  half (dyadic z (succⁿ n) p) | inl q rewrite q = exfalsoₚ (trec {P = ⊥ₚ} (λ { (inl ()) ; (inr ()) }) p)
  half (dyadic z (succⁿ n) p) | inr q = dyadic z (succⁿ (succⁿ n)) ∣ inl q ∣

  -- numbers
  0,0 : Dyadic
  0,0 = dyadic zeroᶻ zeroⁿ ∣ inr refl ∣

  1,0 : Dyadic
  1,0 = dyadic (pos zeroⁿ) zeroⁿ ∣ inr refl ∣

  0,1 : Dyadic
  0,1 = half 1,0

  0,01 : Dyadic
  0,01 = half 0,1

  -- Half of zero
  halfzero : half 0,0 ≡ 0,0
  halfzero = refl

  -- Addition
  {-# TERMINATING #-}
  _+_ : Dyadic → Dyadic → Dyadic
  dyadic z zeroⁿ p + dyadic z' zeroⁿ p' = dyadic (z +ᶻ z') 0 ∣ inr refl ∣
  dyadic z zeroⁿ p + dyadic z' (succⁿ n') p' = dyadic (exp2 (succⁿ n') *ᶻ z +ᶻ z') (succⁿ n') p'
  dyadic z (succⁿ n) p + dyadic z' zeroⁿ p' = dyadic (exp2 (succⁿ n) *ᶻ z' +ᶻ z) (succⁿ n) p
  dyadic z (succⁿ n) p + dyadic z' (succⁿ n') p' =
    half (dyadic z n (Norm-succ z n p) + dyadic z' n' (Norm-succ z' n' p'))
  -- dyadic z n p + dyadic z' n' p' = plus z n p z' n' p'
  --   where
  --     plus : (z : ℤ) → (n : ℕ) → Prf (Norm z n)
  --       → (z' : ℤ) → (n' : ℕ) → Prf (Norm z' n')
  --       → Dyadic
  --     plus z zeroⁿ p z' zeroⁿ p' = dyadic (z +ᶻ z') 0 ∣ inr refl ∣
  --     plus z zeroⁿ p z' (succⁿ n') p' = dyadic (exp2 (succⁿ n') *ᶻ z +ᶻ z') (succⁿ n') p'
  --     plus z (succⁿ n) p z' zeroⁿ p' = dyadic (exp2 (succⁿ n) *ᶻ z' +ᶻ z) (succⁿ n) p
  --     plus z (succⁿ n) p z' (succⁿ n') p' = half (plus z n (Norm-succ z n p) z' n' (Norm-succ z' n' p'))

  mean : Dyadic → Dyadic → Dyadic
  mean d d' = half (d + d')

  asdf : 0,1 + (- 0,01) ≡ 0,01
  asdf = drefl

  +lzero : (d : Dyadic) → 0,0 + d ≡ d
  +lzero (dyadic m zeroⁿ e) = drefl
  +lzero (dyadic m (succⁿ n) e) = refl
  {-# REWRITE +lzero #-}

  +rzero : (d : Dyadic) → d + 0,0 ≡ d
  +rzero (dyadic m zeroⁿ n) = drefl
  +rzero (dyadic m (succⁿ e) n) = refl
  {-# REWRITE +rzero #-}

  -- Multiplication
  {-# TERMINATING #-}
  _*_ : Dyadic → Dyadic → Dyadic
  dyadic z zeroⁿ p * dyadic z' zeroⁿ p' = dyadic (z *ᶻ z') zeroⁿ ∣ inr refl ∣
  dyadic z zeroⁿ p * dyadic z' (succⁿ n') p' = half (dyadic z zeroⁿ p * dyadic z' n' (Norm-succ z' n' p'))
  dyadic z (succⁿ n) p * dyadic z' n' p' = half (dyadic z n (Norm-succ z n p) * dyadic z' n' p') 
  -- dyadic z n p * dyadic z' n' p' = mult z n p z' n' p'
  --   where
  --     mult : (z : ℤ) → (n : ℕ) → Prf (Norm z n)
  --       → (z' : ℤ) → (n' : ℕ) → Prf (Norm z' n')
  --       → Dyadic
  --     mult z zeroⁿ p z' zeroⁿ p' = dyadic (z *ᶻ z') zeroⁿ ∣ inr refl ∣
  --     mult z zeroⁿ p z' (succⁿ n') p' = half (mult z zeroⁿ p z' n' (Norm-succ z' n' p'))
  --     mult z (succⁿ n) p z' n' p' = half (mult z n (Norm-succ z n p) z' n' p')

  {-# TERMINATING #-}
  *lzero : (d : Dyadic) → 0,0 * d ≡ 0,0
  *lzero (dyadic z zeroⁿ p) = refl
  *lzero (dyadic z (succⁿ n) p) = ap half (*lzero (dyadic z n (Norm-succ z n p)))
  {-# REWRITE *lzero #-}

  {-# TERMINATING #-}
  *rzero : (d : Dyadic) → d * 0,0 ≡ 0,0
  *rzero (dyadic z zeroⁿ p) = refl
  *rzero (dyadic z (succⁿ n) p) = ap half (*rzero (dyadic z n (Norm-succ z n p)))
  {-# REWRITE *rzero #-}

  -- Ordering
  _<_ : Dyadic → Dyadic → Bool
  dyadic m e n < dyadic m' e' n' = (m *ᶻ exp2 e' <ᶻ m' *ᶻ exp2 e)

  <halfpos : (d : Dyadic) → 0,0 < (half d) ≡ 0,0 < d
  <halfpos (dyadic z zeroⁿ p) with (even z)??
  <halfpos (dyadic z zeroⁿ p) | inl x = refl
  <halfpos (dyadic z zeroⁿ p) | inr x = refl
  <halfpos (dyadic z (succⁿ n) p) with (even z)??
  <halfpos (dyadic z (succⁿ n) p) | inl x =
    exfalsoₚ (trec {P = ⊥ₚ} (λ { (inl q) → contr (x , q) ; (inr ()) }) p)
  <halfpos (dyadic z (succⁿ n) p) | inr x = refl
  {-# REWRITE <halfpos #-}

  <plusone : ∀ d → d < (1,0 + d) ≡ tt
  <plusone (dyadic z zeroⁿ p) = refl
  <plusone (dyadic z (succⁿ n) p) = 
    begin
      ((z *ᶻ (exp2 n +ᶻ exp2 n)) <ᶻ ((exp2 n +ᶻ exp2 n +ᶻ z) *ᶻ (exp2 n +ᶻ exp2 n)))
        ≡⟨ <*Posn-r (exp2 n +ᶻ exp2 n) z (exp2 n +ᶻ exp2 n +ᶻ z) (<+Pos (exp2 n) (exp2 n) refl refl)
           (begin
             (z <ᶻ (exp2 n +ᶻ exp2 n +ᶻ z)) ≡⟨ refl ⟩
             z <ᶻ ((exp2 n +ᶻ exp2 n) +ᶻ z) ≡⟨ refl ⟩
             zeroᶻ +ᶻ z <ᶻ (exp2 n +ᶻ exp2 n) +ᶻ z ≡⟨ <plus-r z zeroᶻ (exp2 n +ᶻ exp2 n) ⟩
             zeroᶻ <ᶻ exp2 n +ᶻ exp2 n ≡⟨ <+Pos (exp2 n) (exp2 n) refl refl ⟩
             tt
           qed) ⟩
      tt
    qed
  {-# REWRITE <plusone #-}


  <plusᵈ : ∀ k d e → (k + d) < (k + e) ≡ d < e
  <plusᵈ (dyadic z zeroⁿ p) (dyadic z₁ zeroⁿ p₁) (dyadic z₂ zeroⁿ p₂) = refl
  <plusᵈ (dyadic z zeroⁿ p) (dyadic z₁ zeroⁿ p₁) (dyadic z₂ (succⁿ n₂) p₂) = {!!}
  <plusᵈ (dyadic z zeroⁿ p) (dyadic z₁ (succⁿ n₁) p₁) (dyadic z₂ zeroⁿ p₂) = {!!}
  <plusᵈ (dyadic z zeroⁿ p) (dyadic z₁ (succⁿ n₁) p₁) (dyadic z₂ (succⁿ n₂) p₂) = {!!}
  <plusᵈ (dyadic z (succⁿ n) p) (dyadic z₁ n₁ p₁) (dyadic z₂ n₂ p₂) = {!!}
  
  -- <ᵈ-*pos : {a c d : Dyadic}
  --   → (0,0 < a) ≡ tt
  --   → (c < d) ≡ tt
  --   → ((a * c) < (a * d)) ≡ tt
  -- <ᵈ-*pos {dyadic z zeroⁿ p} {dyadic z' zeroⁿ p'} {dyadic z'' zeroⁿ p''} α β = {!!}
  -- <ᵈ-*pos {dyadic z zeroⁿ p} {dyadic z' zeroⁿ p'} {dyadic z'' (succⁿ n'') p''} α β = {!!}
  -- <ᵈ-*pos {dyadic z zeroⁿ p} {dyadic z' (succⁿ n') p'} {dyadic z'' n'' p''} α β = {!!}
  -- <ᵈ-*pos {dyadic z (succⁿ n₁) p} {dyadic z' n' p'} {dyadic z'' n'' p''} α β = {!!}

  
