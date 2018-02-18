{-# OPTIONS --rewriting #-}

open import Base hiding (_+_)
open import Prop
open import Equality
open import naturals.Naturals
open import integers.Definition
open import integers.Successor
open import integers.Addition
open import integers.Multiplication


module integers.Ordering where

  -- Ordering
  _<_ : ℤ → ℤ → Prop
  zero < zero = ⊥ₚ
  zero < pos x = ⊤ₚ
  zero < neg x = ⊥ₚ
  pos x < zero = ⊥ₚ
  pos x < pos y = x <ⁿ y
  pos x < neg y = ⊥ₚ
  neg x < zero = ⊤ₚ
  neg x < pos y = ⊤ₚ
  neg x < neg y = y <ⁿ x

  <trans : ∀ a b c → Prf ((a < b) ~> (b < c) ~> (a < c))
  <trans zero zero c p q = q
  <trans zero (pos x) zero p q = q
  <trans zero (pos x) (pos x₁) p q = **
  <trans zero (pos x) (neg x₁) p q = q
  <trans zero (neg x) zero p q = p
  <trans zero (neg x) (pos x₁) p q = **
  <trans zero (neg x) (neg x₁) p q = p
  <trans (pos x) zero zero p q = q
  <trans (pos x) zero (pos x₁) () q
  <trans (pos x) zero (neg x₁) () q
  <trans (pos x) (pos y) zero p q = q
  <trans (pos x) (pos y) (pos z) p q = <transⁿ x y z p q
  <trans (pos x) (pos y) (neg z) p ()
  <trans (pos x) (neg y) c () q
  <trans (neg x) zero zero p ()
  <trans (neg x) zero (pos x₁) p q = **
  <trans (neg x) zero (neg x₁) p ()
  <trans (neg x) (pos x₁) zero p q = **
  <trans (neg x) (pos x₁) (pos x₂) p q = **
  <trans (neg x) (pos x₁) (neg x₂) p ()
  <trans (neg x) (neg x₁) zero p q = **
  <trans (neg x) (neg x₁) (pos x₂) p q = **
  <trans (neg x) (neg y) (neg z) p q = <transⁿ z y x q p


  Pos : ℤ → Prop
  Pos z = zero < z

  Neg : ℤ → Prop
  Neg z = z < zero

  <succpos : (a : ℤ) → Prf (Pos a ~> Pos (succ a))
  <succpos zero p = **
  <succpos (pos x) p = **
  <succpos (neg x) ()

  <+pos : (a b : ℤ) → Prf (Pos a ~> Pos b ~> Pos (a + b))
  <+pos zero b p q = q
  <+pos (pos a) zero p q = **
  <+pos (pos zeroⁿ) (pos b) p q = **
  <+pos (pos (succⁿ a)) (pos b) p q = <succpos (pos a + pos b) (<+pos (pos a) (pos b) ** **)
  <+pos (pos a) (neg b) p ()
  <+pos (neg a) b () q

  pos-neg : ∀ a → Prf (Pos a ~> Neg (- a))
  pos-neg zero p = p
  pos-neg (pos x) p = **
  pos-neg (neg x) p = p

  neg-pos : ∀ a → Prf (Pos (- a) ~> Neg a)
  neg-pos a = pos-neg (- a)



  <posneg : ∀ a b → Prf (Neg a ~> Pos b ~> (a < b))
  <posneg a b = <trans a zero b

  <succ : ∀ n m → Prf ((succ n < succ m) ~> (n < m))
  <succ zero zero p = p 
  <succ zero (pos x) p = **
  <succ zero (neg zeroⁿ) p = p
  <succ zero (neg (succⁿ x)) p = p
  <succ (pos x) zero p = p
  <succ (pos x) (pos m) p = p
  <succ (pos x) (neg zeroⁿ) p = p
  <succ (pos x) (neg (succⁿ m)) p = p
  <succ (neg x) zero p = **
  <succ (neg x) (pos zeroⁿ) p = **
  <succ (neg x) (pos (succⁿ m)) p = **
  <succ (neg zeroⁿ) (neg zeroⁿ) p = p
  <succ (neg zeroⁿ) (neg (succⁿ m)) p = p
  <succ (neg (succⁿ x)) (neg zeroⁿ) p = **
  <succ (neg (succⁿ x)) (neg (succⁿ m)) p = p

  <succ' : ∀ n m → Prf ((n < m) ~> (succ n < succ m))
  <succ' zero zero p = p
  <succ' zero (pos x) p = **
  <succ' zero (neg x) ()
  <succ' (pos x) zero p = p
  <succ' (pos x) (pos x₁) p = p
  <succ' (pos x) (neg x₁) ()
  <succ' (neg zeroⁿ) zero p = **
  <succ' (neg (succⁿ x)) zero p = **
  <succ' (neg zeroⁿ) (pos x₁) p = **
  <succ' (neg (succⁿ x)) (pos x₁) p = **
  <succ' (neg zeroⁿ) (neg m) p = exfalsoₚ (≥zeroⁿ m p)
  <succ' (neg (succⁿ x)) (neg zeroⁿ) p = **
  <succ' (neg (succⁿ x)) (neg (succⁿ m)) p = p

  <pred : ∀ n m → Prf ((pred n < pred m) ~> (n < m))
  <pred n m = <succ' (pred n) (pred m)

  <pred' : ∀ n m → Prf ((n < m) ~> (pred n < pred m))
  <pred' n m = <succ (pred n) (pred m)

  <plus : ∀ k n m → Prf ((n < m) ~> ((k + n) < (k + m)))
  <plus zero n m p = p
  <plus (pos zeroⁿ) n m p = <succ' n m p
  <plus (pos (succⁿ x)) n m p = <succ' (pos x + n) (pos x + m) (<plus (pos x) n m p)
  <plus (neg zeroⁿ) n m p = <pred' n m p
  <plus (neg (succⁿ x)) n m p = <pred' (neg x + n) (neg x + m) (<plus (neg x) n m p)

  <+neg : ∀ a b → Prf (Neg a ~> Neg b ~> Neg (a + b))
  <+neg a b p q = <trans (a + b) a zero (<plus a b zero q) p

  <*pospos : (a b : ℤ) → Prf (Pos a ~> Pos b ~> Pos (a * b))
  <*pospos zero (b) p q = p
  <*pospos (pos x) zero p q = q
  <*pospos (pos zeroⁿ) (pos y) p q = **
  <*pospos (pos (succⁿ x)) (pos y) p q = <+pos (pos x * pos y) (pos y) (<*pospos (pos x) (pos y) ** **) **
  <*pospos (pos x) (neg y) p ()
  <*pospos (neg x) b () q

  <*posneg : ∀ a b → Prf (Pos a ~> Neg b ~> Neg (a * b))
  <*posneg zero b p q = p
  <*posneg (pos zeroⁿ) b p q = q
  <*posneg (pos (succⁿ x)) b p q = <+neg (pos x * b) b (<*posneg (pos x) b ** q) q
  <*posneg (neg x) b () q

  <*pos : (a c d : ℤ) → Prf ((zero < a) ~> (c < d) ~> ((a * c) < (a * d)))
  <*pos zero c d p q = p
  <*pos (pos x) zero zero p q = q
  <*pos (pos x) zero (pos d) p q = <*pospos (pos x) (pos d) ** **
  <*pos (pos x) zero (neg d) p ()
  <*pos (pos x) (pos zeroⁿ) zero p q = q
  <*pos (pos x) (pos zeroⁿ) (pos zeroⁿ) p q = exfalsoₚ (≥zeroⁿ 0 q)
  <*pos (pos x) (pos zeroⁿ) (pos (succⁿ d)) p q = <plus (pos x) zero (pos x * pos d) (<*pospos (pos x) (pos d) _ _)
  <*pos (pos x) (pos zeroⁿ) (neg d) p ()
  <*pos (pos x) (pos (succⁿ c)) zero p ()
  <*pos (pos x) (pos (succⁿ c)) (pos zeroⁿ) p q = exfalsoₚ (≥zeroⁿ (succⁿ c) q)
  <*pos (pos x) (pos (succⁿ c)) (pos (succⁿ d)) p q = <plus (pos x) (pos x * pos c) (pos x * pos d) (<*pos (pos x) (pos c) (pos d) ** q)
  <*pos (pos x) (pos (succⁿ c)) (neg d) p ()
  <*pos (pos x) (neg zeroⁿ) zero p q = **
  <*pos (pos x) (neg zeroⁿ) (pos d) p q = <posneg (neg x) (pos x * pos d) ** (<*pospos (pos x) (pos d) ** **)
  <*pos (pos x) (neg zeroⁿ) (neg d) p ()
  <*pos (pos x) (neg (succⁿ c)) zero p q = <+neg (neg x) (pos x * neg c) ** (<*posneg (pos x) (neg c) ** **)
  <*pos (pos x) (neg (succⁿ c)) (pos d) p q = <posneg (neg x + pos x * neg c) (pos x * pos d) (<+neg (neg x) (pos x * neg c) ** (<*posneg (pos x) (neg c) ** **)) (<*pospos (pos x) (pos d) ** **)
  <*pos (pos x) (neg (succⁿ c)) (neg zeroⁿ) p q = <plus (neg x) (pos x * neg c) zero (<*posneg (pos x) (neg c) ** **)
  <*pos (pos x) (neg (succⁿ c)) (neg (succⁿ d)) p q = <plus (neg x) (pos x * neg c) (pos x * neg d) (<*pos (pos x) (neg c) (neg d) ** q)
  <*pos (neg x) c d () q
