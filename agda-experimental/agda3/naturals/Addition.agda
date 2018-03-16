{-# OPTIONS --rewriting #-}

open import Equality
open import naturals.Definition

module naturals.Addition where
 
  -- Definition of addition
  _+_ : ℕ → ℕ → ℕ
  0 + m = m
  succ n + m = succ (n + m)

  +rzero : ∀ n → n + 0 ≡ n
  +rzero 0 = refl
  +rzero (succ n) = ap succ (+rzero n)
  {-# REWRITE +rzero #-}

  +rsucc : ∀ n m → n + succ m ≡ succ n + m
  +rsucc zero m = refl
  +rsucc (succ n) m = ap succ (+rsucc n m)
  {-# REWRITE +rsucc #-}

  +assoc : ∀ n m o → n + (m + o) ≡ (n + m) + o
  +assoc zero m o = refl
  +assoc (succ n) m o = ap succ (+assoc n m o)
  {-# REWRITE +assoc #-}

  +comm : ∀ n m → n + m ≡ m + n
  +comm zero m = refl
  +comm (succ n) m = ap succ (+comm n m)
