{-# OPTIONS --rewriting #-}

module Naturals where

open import base.Prop public
open import base.Base renaming (_+ⁿ_ to _+_) public
open import base.Bool renaming (_≡?_ to _≡?ᵇ_ ; from≡? to from≡?ᵇ ; to≡? to to≡?ᵇ) public
open import base.Equality public



-- Decidable equality
succinj : (n m : ℕ) → (succ n ≡ succ m) → n ≡ m
succinj n .n refl = refl

dec≡ : {n m : ℕ} → (n ≡ m) ⊎ (¬ (n ≡ m))
dec≡ {zero} {zero} = inl refl
dec≡ {zero} {succ m} = inr (λ ())
dec≡ {succ n} {zero} = inr (λ ())
dec≡ {succ n} {succ m} with (dec≡ {n} {m})
dec≡ {succ n} {succ m} | inl x = inl (ap succ x)
dec≡ {succ n} {succ m} | inr x = inr λ q → x (succinj n m q)



-- Boolean equality
infix 5 _≡?_
_≡?_ : (n m : ℕ) → Bool
zero ≡? zero = true
zero ≡? succ m = false
succ n ≡? zero = false
succ n ≡? succ m = n ≡? m

from≡? : {n m : ℕ} → (n ≡? m) ≡ true → n ≡ m
from≡? {zero} {zero} p = refl 
from≡? {zero} {succ m} ()
from≡? {succ n} {zero} ()
from≡? {succ n} {succ m} p rewrite (from≡? {n} {m} p) = refl

true≢false : true ≡ false → ⊥
true≢false ()

to≡? : {n m : ℕ} → (n ≡ m) → (n ≡? m) ≡ true
to≡? {zero} {.0} refl = refl
to≡? {succ n} {.(succ n)} refl = to≡? {n} {n} refl

from≢? : {n m : ℕ} → (n ≡? m) ≡ false → ¬ (n ≡ m)
from≢? {n} {m} p q rewrite (to≡? q) = true≢false p

to≢? : {n m : ℕ} → ((n ≡ m) → ⊥) → (n ≡? m) ≡ false
to≢? {zero} {zero} p = exfalso (p refl)
to≢? {zero} {succ m} p = refl
to≢? {succ n} {zero} p = refl
to≢? {succ n} {succ m} p = to≢? {n} {m} λ x → p (ap succ x)

≡?refl : ∀ n → (n ≡? n) ≡ true
≡?refl zero = refl
≡?refl (succ n) = ≡?refl n
{-# REWRITE ≡?refl #-}

≡?symm-b : (n m : ℕ) {b : Bool} → (n ≡? m) ≡ b → (m ≡? n) ≡ b 
≡?symm-b n m {false} p with (from≢? {n} {m} p)
... | w = to≢? {m} {n} λ x → w (inv x)
≡?symm-b n m {true} p rewrite (from≡? {n} {m} p) = refl

≡?symm : ∀ n m → (n ≡? m) ≡ (m ≡? n)
≡?symm n m = ≡?symm-b m n refl

≡?trans-l : ∀ a b c → (a ≡? b) ≡ true → (a ≡? c) ≡ (b ≡? c)
≡?trans-l zero zero c p = refl
≡?trans-l zero (succ b) c ()
≡?trans-l (succ a) zero c ()
≡?trans-l (succ a) (succ b) zero p = refl
≡?trans-l (succ a) (succ b) (succ c) p = ≡?trans-l a b c p

≡?trans-r : ∀ a b c → (a ≡? b) ≡ true → (c ≡? a) ≡ (c ≡? b)
≡?trans-r zero zero c p = refl
≡?trans-r zero (succ b) c ()
≡?trans-r (succ a) zero c ()
≡?trans-r (succ a) (succ b) zero p = refl
≡?trans-r (succ a) (succ b) (succ c) p = ≡?trans-r a b c p



-- Successor
≡-succ : ∀ a → (a ≡? succ a) ≡ false
≡-succ zero = refl
≡-succ (succ a) = ≡-succ a
{-# REWRITE ≡-succ #-}

+onezero-r : ∀ n → (0 ≡? n + 1) ≡ false
+onezero-r zero = refl
+onezero-r (succ n) = refl
{-# REWRITE +onezero-r #-}

+one-r : ∀ n m → (succ n ≡? m + 1) ≡ (n ≡? m)
+one-r n zero = refl
+one-r zero (succ m) = refl
+one-r (succ n) (succ m) = +one-r n m
{-# REWRITE +one-r #-}

+succ-r : ∀ n m → (0 ≡? n + succ m) ≡ false
+succ-r zero m = refl
+succ-r (succ n) m = refl
{-# REWRITE +succ-r #-}

+succ-r-l : ∀ n m → (n + succ m ≡? 0) ≡ false
+succ-r-l n m = ≡?symm-b zero (n + succ m) refl
{-# REWRITE +succ-r-l #-}


-- Addition
+rzero-l : ∀ n n' → (n + 0 ≡? n') ≡ (n ≡? n') 
+rzero-l zero n' = refl
+rzero-l (succ n) zero = refl
+rzero-l (succ n) (succ n') = +rzero-l n n'
{-# REWRITE +rzero-l #-}

+rzero-r : ∀ n n' → (n ≡? n' + 0) ≡ (n ≡? n')
+rzero-r n n' = ≡?symm-b (n' + 0) (n) (≡?symm n' n)
{-# REWRITE +rzero-r #-}

+rsucc : ∀ n m → (n + succ m ≡? succ (n + m)) ≡ true
+rsucc zero m = refl
+rsucc (succ n) m = +rsucc n m
{-# REWRITE +rsucc #-}

+rsucc-r : ∀ n m → (succ (n + m) ≡? n + succ m) ≡ true
+rsucc-r n m = ≡?symm-b (n + succ m) (succ (n + m)) (+rsucc n m)
{-# REWRITE +rsucc-r #-}

+zero-inter : ∀ a b c → (a ≡? b + zero + c) ≡ (a ≡? b + c)
+zero-inter a zero c = refl
+zero-inter zero (succ b) c = refl
+zero-inter (succ a) (succ b) c = +zero-inter a b c
{-# REWRITE +zero-inter #-}


+rsucc-elim-r : ∀ k n m → (succ k ≡? n + succ m) ≡ (k ≡? n + m)
+rsucc-elim-r k zero m = refl
+rsucc-elim-r zero (succ n) m = refl
+rsucc-elim-r (succ k) (succ n) m = +rsucc-elim-r k n m
{-# REWRITE +rsucc-elim-r #-}

+rsucc-elim-l : ∀ k n m → (n + succ m ≡? succ k) ≡ (n + m ≡? k)
+rsucc-elim-l k n m = ≡?symm-b (succ k) (n + succ m) (≡?symm k (n + m))
{-# REWRITE +rsucc-elim-l #-}

+rsucc-both : ∀ a b c d → (a + succ b ≡? c + succ d) ≡ (a + b ≡? c + d)
+rsucc-both zero b c d = refl
+rsucc-both (succ a) b zero zero = refl
+rsucc-both (succ a) b zero (succ d) = +rsucc-both a b zero d
+rsucc-both (succ a) b (succ c) d = +rsucc-both a b c d
{-# REWRITE +rsucc-both #-}

+assoc-r : ∀ n m o → (n + (m + o) ≡? (n + m) + o) ≡ true
+assoc-r zero m o = refl
+assoc-r (succ n) m o = +assoc-r n m o
{-# REWRITE +assoc-r #-}

+assoc-l : ∀ n m o → ((n + m) + o ≡? n + (m + o)) ≡ true
+assoc-l n m o = ≡?symm-b (n + (m + o)) (n + m + o) refl
{-# REWRITE +assoc-l #-}

+assoc-elim-l : ∀ n m o m' o' → (n + (m + o) ≡? (n + m') + o') ≡ (m + o ≡? m' + o')
+assoc-elim-l zero m o m' o' = refl
+assoc-elim-l (succ n) m o m' o' = +assoc-elim-l n m o m' o'
{-# REWRITE +assoc-elim-l #-}

+zerosucc-inter : ∀ a b c → 0 ≡? a + succ b + c ≡ false
+zerosucc-inter zero b c = refl
+zerosucc-inter (succ a) b c = refl
{-# REWRITE +zerosucc-inter #-}

+succ-inter-z : ∀ a b c d → (succ a ≡? b + succ c + d) ≡ (a ≡? b + c + d)
+succ-inter-z a zero c d = refl
+succ-inter-z zero (succ b) c d = refl
+succ-inter-z (succ a) (succ b) c d = +succ-inter-z a b c d
{-# REWRITE +succ-inter-z #-}

+succ-out : ∀ a b c →
  (a   + succ b ≡? c) ≡
  (succ (a + b) ≡? c)
+succ-out zero b c = refl
+succ-out (succ a) b zero = refl
+succ-out (succ a) b (succ c) = +succ-out a b c
{-# REWRITE +succ-out #-}

+succ-plus : ∀ a b → (succ (a + b) ≡? a) ≡ false
+succ-plus zero b = refl
+succ-plus (succ a) b = +succ-plus a b
{-# REWRITE +succ-plus #-}

+assoc-elim-r : ∀ m n o n' o' → (n + (m + o) ≡? (n' + m) + o') ≡ (n + o ≡? n' + o')
+assoc-elim-r zero n o n' o' = refl
+assoc-elim-r (succ m) n o n' o' = +assoc-elim-r m n o n' o'
{-# REWRITE +assoc-elim-r #-}

+comm : ∀ n m → (n + m ≡? m + n) ≡ true
+comm zero m = refl
+comm (succ n) m = +comm n m
{-# REWRITE +comm #-}

+comm-l : ∀ a b c → (a + b ≡? a + c) ≡ (b ≡? c)
+comm-l zero b c = refl
+comm-l (succ a) b c = +comm-l a b c
{-# REWRITE +comm-l #-}

+comm-r : ∀ a b c →
  (b + a ≡? c + a) ≡
  (b     ≡? c)
+comm-r zero b c = refl
+comm-r (succ a) b c = +comm-r a b c
{-# REWRITE +comm-r #-}

+assoc-inter : ∀ a b c d → (a + (b + c) ≡? b + d) ≡ (a + c ≡? d)
+assoc-inter a zero c d = refl
+assoc-inter a (succ b) c d = +assoc-inter a b c d
{-# REWRITE +assoc-inter #-}

+succ-false-r : ∀ a b → a ≡? a + succ b ≡ false
+succ-false-r zero b = refl
+succ-false-r (succ a) b = +succ-false-r a b
{-# REWRITE +succ-false-r #-}

+comm-succ-false : ∀ a b c → (a + b ≡? b + a + succ c) ≡ false
+comm-succ-false zero b c = refl
+comm-succ-false (succ a) b c = +comm-succ-false a b c
{-# REWRITE +comm-succ-false #-}

+succ-false-l : ∀ m n a → succ (m + n + a) ≡? n + m ≡ false
+succ-false-l zero n a = refl
+succ-false-l (succ m) n a = +succ-false-l m n a
{-# REWRITE +succ-false-l #-}

+comm2 : ∀ n m a b →
  (m + n + a ≡? n + m + b) ≡
          (a ≡? b)
+comm2 n m zero zero = refl
+comm2 n m zero (succ b) = refl
+comm2 n m (succ a) zero = refl
+comm2 n m (succ a) (succ b) = +comm2 n m a b
{-# REWRITE +comm2 #-}

+assoc-simpl : ∀ a b c d → (a + b ≡? c + (a + d)) ≡ (b ≡? c + d)
+assoc-simpl zero b c d = refl
+assoc-simpl (succ a) b c d = +assoc-simpl a b c d
{-# REWRITE +assoc-simpl #-}



-- Multiplication
*rzero-l : ∀ n → (n * zero ≡? zero) ≡ true
*rzero-l zero = refl
*rzero-l (succ n) = *rzero-l n
{-# REWRITE *rzero-l #-}

*rzero-r : ∀ n → (zero ≡? n * zero) ≡ true
*rzero-r n = ≡?symm-b (n * zero) zero refl
{-# REWRITE *rzero-r #-}

*runit-l : ∀ n → (n * 1 ≡? n) ≡ true
*runit-l zero = refl
*runit-l (succ n) = *runit-l n
{-# REWRITE *runit-l #-}

*runit-br : ∀ n m → (n * 1 ≡? m) ≡ (n ≡? m)
*runit-br zero m = refl
*runit-br (succ n) zero = refl
*runit-br (succ n) (succ m) = *runit-br n m
{-# REWRITE *runit-br #-}

*runit-bl : ∀ n m → (n ≡? m * 1) ≡ (n ≡? m)
*runit-bl n m = ≡?symm-b (m * 1) n (≡?symm m n)
{-# REWRITE *runit-bl #-}

*inj-r : ∀ a b c → (a * succ b ≡? c * succ b) ≡ (a ≡? c)
*inj-r a zero c = refl
*inj-r zero (succ b) zero = refl
*inj-r zero (succ b) (succ c) = refl
*inj-r (succ a) (succ b) zero = refl
*inj-r (succ a) (succ b) (succ c) = *inj-r a (succ b) c
{-# REWRITE *inj-r #-}

*succ-dist : ∀ m n → m * succ n ≡? m + m * n ≡ true
*succ-dist zero n = refl
*succ-dist (succ m) n = *succ-dist m n
{-# REWRITE *succ-dist #-}

*succ-r : ∀ n m → (m + n * m ≡? m * succ n) ≡ (m + n * m ≡? m + m * n)
*succ-r n m = ≡?trans-r (m * succ n) (m + m * n) (m + n * m) refl
{-# REWRITE *succ-r #-}

*rone-l : ∀ n m → m + m * n ≡? m * succ n ≡ true
*rone-l n zero = refl
*rone-l n (succ m) = *rone-l n m
{-# REWRITE *rone-l #-}

*comm : ∀ n m → (n * m ≡? m * n) ≡ true
*comm zero m = refl
*comm (succ n) m = *comm n m
{-# REWRITE *comm #-}
