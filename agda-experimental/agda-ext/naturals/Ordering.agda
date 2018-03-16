{-# OPTIONS --rewriting #-}

open import Base hiding (_+_)
open import Bool
open import Prop
open import Equality
open import naturals.Definition
open import naturals.Addition
open import naturals.Multiplication

module naturals.Ordering where

  -- Ordering
  infixl 5 _<_ 
  _<_ : ℕ → ℕ → Bool
  m < zero = ff
  zero < succ m = tt
  succ n < succ m = n < m

  infixl 5 _≤_ 
  _≤_ : (n m : ℕ) → Bool
  n ≤ m = ~ (m < n)

  <plus : ∀ k n m → (k + n < k + m) ≡ (n < m)
  <plus zero n m = refl
  <plus (succ k) n m = <plus k n m
  {-# REWRITE <plus #-}

  <plus-r : ∀ k n m → (n + k < m + k) ≡ (n < m)
  <plus-r zero n m = refl
  <plus-r (succ k) n m = <plus-r k n m
  {-# REWRITE <plus-r #-}

  ≤plus : ∀ k n m → (k + n ≤ k + m) ≡ (n ≤ m)
  ≤plus k n m = refl

  ≤plus-r : ∀ k n m → (n + k ≤ m + k) ≡ (n ≤ m)
  ≤plus-r k n m = refl

  <trans : ∀ n m k
    → (n < m) ≡ tt
    → (m < k) ≡ tt
    → (n < k) ≡ tt
  <trans zero zero k p q = q
  <trans zero (succ m) zero p q = q
  <trans zero (succ m) (succ k) p q = refl
  <trans (succ n) zero zero p q = q
  <trans (succ n) zero (succ k) () q
  <trans (succ n) (succ m) zero p q = q
  <trans (succ n) (succ m) (succ k) p q = <trans n m k p q

  ≤trans : ∀ n m k
    → (n ≤ m) ≡ tt
    → (m ≤ k) ≡ tt
    → (n ≤ k) ≡ tt
  ≤trans zero m k p q = refl
  ≤trans (succ n) zero k () q
  ≤trans (succ n) (succ m) zero p ()
  ≤trans (succ n) (succ m) (succ k) p q = ≤trans n m k p q
    
  <mult : ∀ n m k → (succ k * n < succ k * m) ≡ (n < m)
  <mult n m zero = refl
  <mult n m (succ k) with (n < m)??
  <mult n m (succ k) | inl f =
    <trans (((k * n) + n) + n) (((k * n) + n) + m) (((k * m) + m) + m) f (<mult n m k · f) · inv f
  <mult n m (succ k) | inr f =
    ap ~ (≤trans (((k * m) + m) + m)
      (((k * m) + m) + n) (((k * n) + n) + n) (ap ~ f) (ap ~ (<mult n m k · f)))
      · inv f
  {-# REWRITE <mult #-}

  <mult-r : ∀ n m k → (n * succ k < m * succ k) ≡ (n < m)
  <mult-r n m k = 
    begin
      ((n * succ k) < (m * succ k)) ≡⟨ ap (λ u → u < (m * succ k)) (*comm n (succ k)) ⟩
      ((succ k * n) < (m * succ k)) ≡⟨ ap (λ u → ((succ k * n) < u)) (*comm m (succ k))  ⟩
      ((succ k * n) < (succ k * m)) ≡⟨ refl ⟩      
      (n < m)
    qed
  {-# REWRITE <mult-r #-}

  -- Propositions
  ≤zero : ∀ n → Prf [ 0 ≤ n ]
  ≤zero n = refl
  
  [<]plus : ∀ k n m → Prf ([ n < m ] ~> [ (k + n) < (k + m) ])
  [<]plus k n m p = p

  [<]trans : ∀ n m k → Prf ([ n < m ] ~> [ m < k ] ~> [ n < k ])
  [<]trans = <trans
