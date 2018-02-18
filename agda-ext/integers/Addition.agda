{-# OPTIONS --rewriting #-}

open import Equality
open import naturals.Naturals
open import integers.Definition
open import integers.Successor

module integers.Addition where

  -- Negation
  - : ℤ → ℤ
  - zero     = zero
  - (pos x) = neg x
  - (neg x) = pos x  

  -double : (z : ℤ) → - (- z) ≡ z
  -double zero = refl
  -double (pos x) = refl
  -double (neg x) = refl
  {-# REWRITE -double #-}


  -- Addition
  infixl 60 _+_
  _+_ : ℤ → ℤ → ℤ
  zero          + m = m
  pos zeroⁿ     + m = succ m
  pos (succⁿ x) + m = succ (pos x + m)
  neg zeroⁿ     + m = pred m
  neg (succⁿ x) + m = pred (neg x + m)

  +rzero : ∀ n → n + zero ≡ n
  +rzero zero            = refl
  +rzero (pos zeroⁿ)     = refl
  +rzero (pos (succⁿ x)) = ap succ (+rzero (pos x))
  +rzero (neg zeroⁿ)     = refl
  +rzero (neg (succⁿ x)) = ap pred (+rzero (neg x))
  {-# REWRITE +rzero #-}

  +onesucc : ∀ n → (n + pos zeroⁿ) ≡ succ n
  +onesucc zero = refl
  +onesucc (pos zeroⁿ) = refl
  +onesucc (pos (succⁿ x)) = ap succ (+onesucc (pos x))
  +onesucc (neg zeroⁿ) = refl
  +onesucc (neg (succⁿ x)) = ap pred (+onesucc (neg x))
  {-# REWRITE +onesucc #-}

  +onepred : ∀ n → (n + neg zeroⁿ) ≡ pred n
  +onepred zero = refl
  +onepred (pos zeroⁿ) = refl
  +onepred (pos (succⁿ x)) = ap succ (+onepred (pos x))
  +onepred (neg zeroⁿ) = refl
  +onepred (neg (succⁿ x)) = ap pred (+onepred (neg x))
  {-# REWRITE +onepred #-}

  +possucc : ∀ n → (x : ℕ) → n + pos (succⁿ x) ≡ succ (n + pos x)
  +possucc zero x = refl
  +possucc (pos zeroⁿ) x = refl
  +possucc (pos (succⁿ n)) x = ap succ (+possucc (pos n) x)
  +possucc (neg zeroⁿ) x = refl
  +possucc (neg (succⁿ n)) x = ap pred (+possucc (neg n) x)
  {-# REWRITE +possucc #-}

  +negpred : ∀ n → (x : ℕ) →  n + neg (succⁿ x) ≡ pred (n + neg x)
  +negpred zero x = refl
  +negpred (pos zeroⁿ) x = refl
  +negpred (pos (succⁿ n)) x = ap succ (+negpred (pos n) x)
  +negpred (neg zeroⁿ) x = refl
  +negpred (neg (succⁿ n)) x = ap pred (+negpred (neg n) x)
  {-# REWRITE +negpred #-}

  +succ : (n m : ℤ) → succ n + m ≡ succ (n + m)
  +succ zero m = refl
  +succ (pos x) m = refl
  +succ (neg zeroⁿ) m = refl
  +succ (neg (succⁿ x)) m = refl
  {-# REWRITE +succ #-}

  +pred : (n m : ℤ) → pred n + m ≡ pred (n + m)
  +pred zero m = refl
  +pred (pos zeroⁿ) m = refl
  +pred (pos (succⁿ x)) m = refl
  +pred (neg x) m = refl
  {-# REWRITE +pred #-}
  
  +assoc : (n m o : ℤ) → n + (m + o) ≡ (n + m) + o
  +assoc zero m o = refl
  +assoc (pos zeroⁿ) m o = refl
  +assoc (pos (succⁿ x)) m o = ap succ (+assoc (pos x) m o)
  +assoc (neg zeroⁿ) m o = refl
  +assoc (neg (succⁿ x)) m o = ap pred (+assoc (neg x) m o)
  {-# REWRITE +assoc #-}

  +opp-r : ∀ n → n + (- n) ≡ zero
  +opp-r zero = refl
  +opp-r (pos zeroⁿ) = refl
  +opp-r (pos (succⁿ x)) = +opp-r (pos x)
  +opp-r (neg zeroⁿ) = refl
  +opp-r (neg (succⁿ x)) = +opp-r (neg x)
  {-# REWRITE +opp-r #-}

  +opp-l : ∀ n → (- n) + n ≡ zero
  +opp-l zero = refl
  +opp-l (pos zeroⁿ) = refl
  +opp-l (pos (succⁿ x)) = +opp-l (pos x)
  +opp-l (neg zeroⁿ) = refl
  +opp-l (neg (succⁿ x)) = +opp-l (neg x)
  {-# REWRITE +opp-l #-}

  +opp-pred : ∀ n → (- (succ n)) ≡ pred (- n)
  +opp-pred zero = refl
  +opp-pred (pos x) = refl
  +opp-pred (neg zeroⁿ) = refl
  +opp-pred (neg (succⁿ x)) = refl
  
  +opp-succ : ∀ n → (- (pred n)) ≡ succ (- n)
  +opp-succ zero = refl
  +opp-succ (pos zeroⁿ) = refl
  +opp-succ (pos (succⁿ x)) = refl
  +opp-succ (neg x) = refl
  {-# REWRITE +opp-pred #-}
  {-# REWRITE +opp-succ #-}

  +opp-plus : ∀ n m → - (n + m) ≡ (- n) + (- m)
  +opp-plus zero m = refl
  +opp-plus (pos x) zero = refl
  +opp-plus (pos zeroⁿ) (pos y) = refl
  +opp-plus (pos (succⁿ x)) (pos y) = ap pred (+opp-plus (pos x) (pos y))
  +opp-plus (pos zeroⁿ) (neg y) = refl
  +opp-plus (pos (succⁿ x)) (neg y) = ap pred (+opp-plus (pos x) (neg y))
  +opp-plus (neg x) zero = refl
  +opp-plus (neg zeroⁿ) (pos m) = refl
  +opp-plus (neg (succⁿ x)) (pos m) = ap succ ((+opp-plus (neg x) (pos m)))
  +opp-plus (neg zeroⁿ) (neg m) = refl
  +opp-plus (neg (succⁿ x)) (neg m) = ap succ (+opp-plus (neg x) (neg m))
  {-# REWRITE +opp-plus #-}

  +comm : (n m : ℤ) → n + m ≡ m + n
  +comm zero m = refl
  +comm (pos zeroⁿ) m = refl
  +comm (pos (succⁿ x)) m = ap succ (+comm (pos x) m)
  +comm (neg zeroⁿ) m = refl
  +comm (neg (succⁿ x)) m = ap pred (+comm (neg x) m)  
