{-# OPTIONS --rewriting #-}

open import Base
open import Equality
open import Naturals
open import Prop

module Integers where

  data ℤ : Set where
    zer : ℤ
    pos : ℕ → ℤ
    neg : ℕ → ℤ  

  NtoZ : ℕ → ℤ
  NtoZ zero     = zer
  NtoZ (succ n) = pos n

  -- Successor and predecessor
  zsucc : ℤ → ℤ
  zsucc zer            = pos 0
  zsucc (pos x)        = pos (succ x)
  zsucc (neg zero)     = zer
  zsucc (neg (succ x)) = neg x

  zpred : ℤ → ℤ
  zpred zer            = neg 0
  zpred (pos zero)     = zer
  zpred (pos (succ x)) = pos x
  zpred (neg x)        = neg (succ x)

  zsuccpred-id : (n : ℤ) → zsucc (zpred n) ≡ n
  zsuccpred-id zer            = refl
  zsuccpred-id (pos zero)     = refl
  zsuccpred-id (pos (succ n)) = refl
  zsuccpred-id (neg n)        = refl
  {-# REWRITE zsuccpred-id #-}

  zpredsucc-id : (n : ℤ) → zpred (zsucc n) ≡ n
  zpredsucc-id zer            = refl
  zpredsucc-id (pos n)        = refl
  zpredsucc-id (neg zero)     = refl
  zpredsucc-id (neg (succ n)) = refl
  {-# REWRITE zpredsucc-id #-}


  -- Negation
  - : ℤ → ℤ
  - zer     = zer
  - (pos x) = neg x
  - (neg x) = pos x  

  double- : (z : ℤ) → - (- z) ≡ z
  double- zer = refl
  double- (pos x) = refl
  double- (neg x) = refl
  {-# REWRITE double- #-}


  -- Addition
  infixl 60 _+ᶻ_
  _+ᶻ_ : ℤ → ℤ → ℤ
  zer          +ᶻ m = m
  pos zero     +ᶻ m = zsucc m
  pos (succ x) +ᶻ m = zsucc (pos x +ᶻ m)
  neg zero     +ᶻ m = zpred m
  neg (succ x) +ᶻ m = zpred (neg x +ᶻ m)

  +ᶻ-rzero : (n : ℤ) → n +ᶻ zer ≡ n
  +ᶻ-rzero zer            = refl
  +ᶻ-rzero (pos zero)     = refl
  +ᶻ-rzero (pos (succ x)) = ap zsucc (+ᶻ-rzero (pos x))
  +ᶻ-rzero (neg zero)     = refl
  +ᶻ-rzero (neg (succ x)) = ap zpred (+ᶻ-rzero (neg x))
  {-# REWRITE +ᶻ-rzero #-}

  +ᶻ-onesucc : (n : ℤ) → (n +ᶻ pos zero) ≡ zsucc n
  +ᶻ-onesucc zer = refl
  +ᶻ-onesucc (pos zero) = refl
  +ᶻ-onesucc (pos (succ x)) = ap zsucc (+ᶻ-onesucc (pos x))
  +ᶻ-onesucc (neg zero) = refl
  +ᶻ-onesucc (neg (succ x)) = ap zpred (+ᶻ-onesucc (neg x))
  {-# REWRITE +ᶻ-onesucc #-}

  +ᶻ-onepred : (n : ℤ) → (n +ᶻ neg zero) ≡ zpred n
  +ᶻ-onepred zer = refl
  +ᶻ-onepred (pos zero) = refl
  +ᶻ-onepred (pos (succ x)) = ap zsucc (+ᶻ-onepred (pos x))
  +ᶻ-onepred (neg zero) = refl
  +ᶻ-onepred (neg (succ x)) = ap zpred (+ᶻ-onepred (neg x))
  {-# REWRITE +ᶻ-onepred #-}

  +ᶻ-possucc : (n : ℤ) → (x : ℕ) → n +ᶻ pos (succ x) ≡ zsucc (n +ᶻ pos x)
  +ᶻ-possucc zer x = refl
  +ᶻ-possucc (pos zero) x = refl
  +ᶻ-possucc (pos (succ n)) x = ap zsucc (+ᶻ-possucc (pos n) x)
  +ᶻ-possucc (neg zero) x = refl
  +ᶻ-possucc (neg (succ n)) x = ap zpred (+ᶻ-possucc (neg n) x)
  {-# REWRITE +ᶻ-possucc #-}

  +ᶻ-negpred : (n : ℤ) → (x : ℕ) →  n +ᶻ neg (succ x) ≡ zpred (n +ᶻ neg x)
  +ᶻ-negpred zer x = refl
  +ᶻ-negpred (pos zero) x = refl
  +ᶻ-negpred (pos (succ n)) x = ap zsucc (+ᶻ-negpred (pos n) x)
  +ᶻ-negpred (neg zero) x = refl
  +ᶻ-negpred (neg (succ n)) x = ap zpred (+ᶻ-negpred (neg n) x)
  {-# REWRITE +ᶻ-negpred #-}

  +ᶻ-comm : (n m : ℤ) → n +ᶻ m ≡ m +ᶻ n
  +ᶻ-comm zer m = refl
  +ᶻ-comm (pos zero) m = refl
  +ᶻ-comm (pos (succ x)) m = ap zsucc (+ᶻ-comm (pos x) m)
  +ᶻ-comm (neg zero) m = refl
  +ᶻ-comm (neg (succ x)) m = ap zpred (+ᶻ-comm (neg x) m)

  +ᶻ-zsucc : (n m : ℤ) → zsucc n +ᶻ m ≡ zsucc (n +ᶻ m)
  +ᶻ-zsucc zer m = refl
  +ᶻ-zsucc (pos x) m = refl
  +ᶻ-zsucc (neg zero) m = refl
  +ᶻ-zsucc (neg (succ x)) m = refl
  {-# REWRITE +ᶻ-zsucc #-}

  +ᶻ-zpred : (n m : ℤ) → zpred n +ᶻ m ≡ zpred (n +ᶻ m)
  +ᶻ-zpred zer m = refl
  +ᶻ-zpred (pos zero) m = refl
  +ᶻ-zpred (pos (succ x)) m = refl
  +ᶻ-zpred (neg x) m = refl
  {-# REWRITE +ᶻ-zpred #-}
  
  +ᶻ-assoc : (n m o : ℤ) → n +ᶻ (m +ᶻ o) ≡ (n +ᶻ m) +ᶻ o
  +ᶻ-assoc zer m o = refl
  +ᶻ-assoc (pos zero) m o = refl
  +ᶻ-assoc (pos (succ x)) m o = ap zsucc (+ᶻ-assoc (pos x) m o)
  +ᶻ-assoc (neg zero) m o = refl
  +ᶻ-assoc (neg (succ x)) m o = ap zpred (+ᶻ-assoc (neg x) m o)
  {-# REWRITE +ᶻ-assoc #-}


  -- Multiplication
  infixl 70 _*ᶻ_
  _*ᶻ_ : ℤ → ℤ → ℤ
  zer *ᶻ m = zer
  pos zero *ᶻ m = m
  pos (succ x) *ᶻ m = (pos x *ᶻ m) +ᶻ m
  neg zero *ᶻ m = - m
  neg (succ x) *ᶻ m = (neg x *ᶻ m) +ᶻ (- m)

  *ᶻ-rzero : (n : ℤ) → n *ᶻ zer ≡ zer
  *ᶻ-rzero zer = refl
  *ᶻ-rzero (pos zero) = refl
  *ᶻ-rzero (pos (succ x)) = *ᶻ-rzero (pos x)
  *ᶻ-rzero (neg zero) = refl
  *ᶻ-rzero (neg (succ x)) = *ᶻ-rzero (neg x)
  {-# REWRITE *ᶻ-rzero #-}

  *ᶻ-rone : (n : ℤ) → n *ᶻ pos zero ≡ n
  *ᶻ-rone zer = refl
  *ᶻ-rone (pos zero) = refl
  *ᶻ-rone (pos (succ x)) = ap zsucc (*ᶻ-rone (pos x))
  *ᶻ-rone (neg zero) = refl
  *ᶻ-rone (neg (succ x)) = ap zpred (*ᶻ-rone (neg x))
  {-# REWRITE *ᶻ-rone #-}

  *ᶻ-rmone : (n : ℤ) → n *ᶻ neg zero ≡ - n
  *ᶻ-rmone zer = refl
  *ᶻ-rmone (pos zero) = refl
  *ᶻ-rmone (pos (succ x)) = ap zpred (*ᶻ-rmone (pos x))
  *ᶻ-rmone (neg zero) = refl
  *ᶻ-rmone (neg (succ x)) = ap zsucc (*ᶻ-rmone (neg x))
  {-# REWRITE *ᶻ-rmone #-}

  *ᶻ-rpossucc : (n : ℕ) → (m : ℤ) → m *ᶻ pos (succ n) ≡ m +ᶻ m *ᶻ pos n
  *ᶻ-rpossucc n zer = refl
  *ᶻ-rpossucc n (pos zero) = refl
  *ᶻ-rpossucc n (pos (succ x)) = ap (λ u → zsucc (u +ᶻ pos n)) (*ᶻ-rpossucc n (pos x))
  *ᶻ-rpossucc n (neg zero) = refl
  *ᶻ-rpossucc n (neg (succ x)) = ap (λ u → zpred (u +ᶻ neg n)) (*ᶻ-rpossucc n (neg x))
  {-# REWRITE *ᶻ-rpossucc #-}

  *ᶻ-rnegsucc : (n : ℕ) → (m : ℤ) → m *ᶻ neg (succ n) ≡ (- m) +ᶻ m *ᶻ neg n
  *ᶻ-rnegsucc n zer = refl
  *ᶻ-rnegsucc n (pos zero) = refl
  *ᶻ-rnegsucc n (pos (succ x)) = ap (λ u → zpred (u +ᶻ neg n)) (*ᶻ-rnegsucc n (pos x))
  *ᶻ-rnegsucc n (neg zero) = refl
  *ᶻ-rnegsucc n (neg (succ x)) = ap (λ u → zsucc (u +ᶻ pos n)) (*ᶻ-rnegsucc n (neg x))
  {-# REWRITE *ᶻ-rnegsucc #-}



  -- Ordering
  _<ᶻ_ : ℤ → ℤ → Prop
  zer <ᶻ zer = ⊥ₚ
  zer <ᶻ pos x = ⊤ₚ
  zer <ᶻ neg x = ⊥ₚ
  pos x <ᶻ zer = ⊥ₚ
  pos x <ᶻ pos y = x <ⁿ y
  pos x <ᶻ neg y = ⊥ₚ
  neg x <ᶻ zer = ⊤ₚ
  neg x <ᶻ pos y = ⊤ₚ
  neg x <ᶻ neg y = y <ⁿ x


  Posᶻ : ℤ → Prop
  Posᶻ z = zer <ᶻ z

  Negᶻ : ℤ → Prop
  Negᶻ z = z <ᶻ zer

  <ᶻ-zsuccpos : (a : ℤ) → Prf (Posᶻ a ~> Posᶻ (zsucc a))
  <ᶻ-zsuccpos zer p = **
  <ᶻ-zsuccpos (pos x) p = **
  <ᶻ-zsuccpos (neg x) ()

  <ᶻ-+pos : (a b : ℤ) → Prf (Posᶻ a ~> Posᶻ b ~> Posᶻ (a +ᶻ b))
  <ᶻ-+pos zer b p q = q
  <ᶻ-+pos (pos a) zer p q = **
  <ᶻ-+pos (pos zero) (pos b) p q = **
  <ᶻ-+pos (pos (succ a)) (pos b) p q = <ᶻ-zsuccpos (pos a +ᶻ pos b) (<ᶻ-+pos (pos a) (pos b) ** **)
  <ᶻ-+pos (pos a) (neg b) p ()
  <ᶻ-+pos (neg a) b () q

  <ᶻ-plus : ∀ k n m → Prf ((n <ᶻ m) ~> ((k +ᶻ n) <ᶻ (k +ᶻ m)))
  <ᶻ-plus zer n m p = p
  <ᶻ-plus (pos zero) zer zer ()
  <ᶻ-plus (pos zero) zer (pos x) p = <ⁿ-zerosucc x
  <ᶻ-plus (pos zero) zer (neg x) ()
  <ᶻ-plus (pos zero) (pos n) zer ()
  <ᶻ-plus (pos zero) (pos n) (pos m) p = <ⁿ-succ n m p
  <ᶻ-plus (pos zero) (pos n) (neg m) ()
  <ᶻ-plus (pos zero) (neg zero) zer p = **
  <ᶻ-plus (pos zero) (neg zero) (pos x) p = **
  <ᶻ-plus (pos zero) (neg zero) (neg x) p = exfalsoₚ (≥ⁿ-zero x p)
  <ᶻ-plus (pos zero) (neg (succ n)) m p = {!!}
  <ᶻ-plus (pos (succ x)) n m p = {!!}
  <ᶻ-plus (neg x) n m p = {!!}

  <ᶻ-*pospos : (a b : ℤ) → Prf (Posᶻ a ~> Posᶻ b ~> Posᶻ (a *ᶻ b))
  <ᶻ-*pospos (zer) (b) p q = p
  <ᶻ-*pospos (pos x) (zer) p q = q
  <ᶻ-*pospos (pos zero) (pos y) p q = **
  <ᶻ-*pospos (pos (succ x)) (pos y) p q = <ᶻ-+pos (pos x *ᶻ pos y) (pos y) (<ᶻ-*pospos (pos x) (pos y) ** **) **
  <ᶻ-*pospos (pos x) (neg y) p ()
  <ᶻ-*pospos (neg x) b () q

  <ᶻ-*pos : (a c d : ℤ) → Prf ((zer <ᶻ a) ~> (c <ᶻ d) ~> ((a *ᶻ c) <ᶻ (a *ᶻ d)))
  <ᶻ-*pos (zer) (c) (d) p q = p
  <ᶻ-*pos (pos x) (zer) (zer) p q = q
  <ᶻ-*pos (pos x) (zer) (pos d) p q = <ᶻ-*pospos (pos x) (pos d) ** **
  <ᶻ-*pos (pos x) zer (neg d) p ()
  <ᶻ-*pos (pos x) (pos zero) zer p q = q
  <ᶻ-*pos (pos x) (pos zero) (pos zero) p q = exfalsoₚ (≥ⁿ-zero 0 q)
  <ᶻ-*pos (pos x) (pos zero) (pos (succ d)) p q = {!<ⁿ-plus!}
  <ᶻ-*pos (pos x) (pos zero) (neg d) p ()
  <ᶻ-*pos (pos x) (pos (succ c)) zer p ()
  <ᶻ-*pos (pos x) (pos (succ c)) (pos zero) p q = exfalsoₚ (≥ⁿ-zero (succ c) q)
  <ᶻ-*pos (pos x) (pos (succ c)) (pos (succ d)) p q = {!<\!}
  <ᶻ-*pos (pos x) (pos (succ c)) (neg d) p ()
  <ᶻ-*pos (pos x) (neg zero) zer p q = **
  <ᶻ-*pos (pos x) (neg zero) (pos d) p q = {!!}
  <ᶻ-*pos (pos x) (neg zero) (neg d) p q = {!!}
  <ᶻ-*pos (pos x) (neg (succ c)) d p q = {!!}
  <ᶻ-*pos (neg x) c d () q
