{-# OPTIONS --rewriting #-}

open import Equality
open import naturals.Naturals
open import integers.Definition
open import integers.Successor
open import integers.Addition

module integers.Multiplication where

  -- Multiplication
  infixl 70 _*_
  _*_ : ℤ → ℤ → ℤ
  zero * m = zero
  pos zeroⁿ * m = m
  pos (succⁿ x) * m = (pos x * m) + m
  neg zeroⁿ * m = - m
  neg (succⁿ x) * m = (neg x * m) + (- m)

  *rzero : ∀ n → n * zero ≡ zero
  *rzero zero = refl
  *rzero (pos zeroⁿ) = refl
  *rzero (pos (succⁿ x)) = *rzero (pos x)
  *rzero (neg zeroⁿ) = refl
  *rzero (neg (succⁿ x)) = *rzero (neg x)
  {-# REWRITE *rzero #-}

  *rone : ∀ n → n * pos zeroⁿ ≡ n
  *rone zero = refl
  *rone (pos zeroⁿ) = refl
  *rone (pos (succⁿ x)) = ap succ (*rone (pos x))
  *rone (neg zeroⁿ) = refl
  *rone (neg (succⁿ x)) = ap pred (*rone (neg x))
  {-# REWRITE *rone #-}

  *-rmone : ∀ n → n * neg zeroⁿ ≡ - n
  *-rmone zero = refl
  *-rmone (pos zeroⁿ) = refl
  *-rmone (pos (succⁿ x)) = ap pred (*-rmone (pos x))
  *-rmone (neg zeroⁿ) = refl
  *-rmone (neg (succⁿ x)) = ap succ (*-rmone (neg x))
  {-# REWRITE *-rmone #-}

  *-rpossucc : (n : ℕ) → (m : ℤ) → m * pos (succⁿ n) ≡ m + m * pos n
  *-rpossucc n zero = refl
  *-rpossucc n (pos zeroⁿ) = refl
  *-rpossucc n (pos (succⁿ x)) = ap (λ u → succ (u + pos n)) (*-rpossucc n (pos x))
  *-rpossucc n (neg zeroⁿ) = refl
  *-rpossucc n (neg (succⁿ x)) = ap (λ u → pred (u + neg n)) (*-rpossucc n (neg x))
  {-# REWRITE *-rpossucc #-}

  *rnegsucc : (n : ℕ) → (m : ℤ) → m * neg (succⁿ n) ≡ (- m) + m * neg n
  *rnegsucc n zero = refl
  *rnegsucc n (pos zeroⁿ) = refl
  *rnegsucc n (pos (succⁿ x)) = ap (λ u → pred (u + neg n)) (*rnegsucc n (pos x))
  *rnegsucc n (neg zeroⁿ) = refl
  *rnegsucc n (neg (succⁿ x)) = ap (λ u → succ (u + pos n)) (*rnegsucc n (neg x))
  {-# REWRITE *rnegsucc #-}
  
  *pos : ∀ n m → pos n * pos m ≡ pos (((n *ⁿ m) +ⁿ n) +ⁿ m)
  *pos zeroⁿ m = refl
  *pos (succⁿ n) m = ap (_+ pos m) (*pos n m) · ap (λ u → pos (succⁿ (((n *ⁿ m) +ⁿ u) +ⁿ m))) (+commⁿ n m)
  {-# REWRITE *pos #-}

  *neg : ∀ n m → neg n * neg m ≡ pos n * pos m
  *neg zeroⁿ m = refl
  *neg (succⁿ n) m = ap (_+ pos m) (*neg n m)
  {-# REWRITE *neg #-}

  *negpos : ∀ n m → neg n * pos m ≡ neg (((n *ⁿ m) +ⁿ n) +ⁿ m)
  *negpos zeroⁿ m = refl
  *negpos (succⁿ n) m = ap (_+ neg m) (*negpos n m) · ap (λ u → neg (succⁿ (((n *ⁿ m) +ⁿ u) +ⁿ m))) (+commⁿ n m)
  {-# REWRITE *negpos #-}

  *posneg : ∀ n m → pos n * neg m ≡ neg (((n *ⁿ m) +ⁿ n) +ⁿ m)
  *posneg zeroⁿ m = refl
  *posneg (succⁿ n) m = ap (_+ neg m) (*posneg n m) · ap (λ u → neg (succⁿ (((n *ⁿ m) +ⁿ u) +ⁿ m))) (+commⁿ n m)
  {-# REWRITE *posneg #-}

  *minus-l : ∀ a b →  - (a * b) ≡ (- a) * b
  *minus-l zero b = refl
  *minus-l (pos x) zero = refl
  *minus-l (pos x) (pos y) = refl
  *minus-l (pos x) (neg y) = refl
  *minus-l (neg x) zero = refl
  *minus-l (neg x) (pos y) = refl
  *minus-l (neg x) (neg y) = refl
  {-# REWRITE *minus-l #-}

  private
    lemma : ∀ n m → ((n *ⁿ m) +ⁿ n) +ⁿ m ≡ ((m *ⁿ n) +ⁿ m) +ⁿ n
    lemma n m = 
      begin
        (((n *ⁿ m) +ⁿ n) +ⁿ m) ≡⟨ ap (λ u → ((u +ⁿ n) +ⁿ m)) (*commⁿ n m) ⟩
        ((m *ⁿ n) +ⁿ (n +ⁿ m)) ≡⟨ ap ((m *ⁿ n) +ⁿ_) (+commⁿ n m) ⟩
        (((m *ⁿ n) +ⁿ m) +ⁿ n)
      qed

  *comm : ∀ a b → a * b ≡ b * a
  *comm zero b = refl
  *comm (pos x) zero = refl
  *comm (pos x) (pos y) = ap pos (lemma x y)
  *comm (pos x) (neg y) = ap neg (lemma x y)
  *comm (neg x) zero = refl
  *comm (neg x) (pos y) = ap neg (lemma x y)
  *comm (neg x) (neg y) = ap pos (lemma x y)
