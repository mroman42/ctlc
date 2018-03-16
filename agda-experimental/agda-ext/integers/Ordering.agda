{-# OPTIONS --rewriting #-}

open import Base hiding (_+_)
open import Prop
open import Bool
open import Equality
open import naturals.Naturals
open import integers.Definition
open import integers.Successor
open import integers.Addition
open import integers.Multiplication
open import integers.Even

module integers.Ordering where

  -- Ordering
  _<_ : ℤ → ℤ → Bool
  zero < zero = ff
  zero < pos x = tt
  zero < neg x = ff
  pos x < zero = ff
  pos x < pos y = x <ⁿ y
  pos x < neg y = ff
  neg x < zero = tt
  neg x < pos y = tt
  neg x < neg y = y <ⁿ x

  Pos : ℤ → Bool
  Pos z = zero < z

  Neg : ℤ → Bool
  Neg z = z < zero

  pos-neg : ∀ a → (- a < zero) ≡ (zero < a)
  pos-neg zero = refl
  pos-neg (pos x) = refl
  pos-neg (neg x) = refl
  {-# REWRITE pos-neg #-}

  neg-pos : ∀ a → (zero < - a) ≡ (a < zero)
  neg-pos zero = refl
  neg-pos (pos x) = refl
  neg-pos (neg x) = refl
  {-# REWRITE neg-pos #-}

  <succ : ∀ n m → (succ n < succ m) ≡ (n < m)
  <succ zero zero = refl
  <succ zero (pos x) = refl
  <succ zero (neg zeroⁿ) = refl
  <succ zero (neg (succⁿ x)) = refl
  <succ (pos x) zero = refl
  <succ (pos x) (pos x₁) = refl
  <succ (pos x) (neg zeroⁿ) = refl
  <succ (pos x) (neg (succⁿ x₁)) = refl
  <succ (neg zeroⁿ) zero = refl
  <succ (neg (succⁿ x)) zero = refl
  <succ (neg zeroⁿ) (pos x₁) = refl
  <succ (neg (succⁿ x)) (pos x₁) = refl
  <succ (neg zeroⁿ) (neg zeroⁿ) = refl
  <succ (neg zeroⁿ) (neg (succⁿ x₁)) = refl
  <succ (neg (succⁿ x)) (neg zeroⁿ) = refl
  <succ (neg (succⁿ x)) (neg (succⁿ x₁)) = refl
  {-# REWRITE <succ #-}

  <pred : ∀ n m → (pred n < pred m) ≡ (n < m)
  <pred n m = inv (<succ (pred n) (pred m))
  {-# REWRITE <pred #-}

  <plus : ∀ k n m → (k + n) < (k + m) ≡ (n < m)
  <plus zero n m = refl
  <plus (pos zeroⁿ) n m = refl
  <plus (pos (succⁿ x)) n m = <plus (pos x) n m
  <plus (neg zeroⁿ) n m = refl
  <plus (neg (succⁿ x)) n m = <plus (neg x) n m
  {-# REWRITE <plus #-}
  
  <plus-r : ∀ k n m → (n + k) < (m + k) ≡ (n < m)
  <plus-r zero n m = refl
  <plus-r (pos zeroⁿ) n m = refl
  <plus-r (pos (succⁿ x)) n m = <plus-r (pos x) n m
  <plus-r (neg zeroⁿ) n m = refl
  <plus-r (neg (succⁿ x)) n m = <plus-r (neg x) n m
  {-# REWRITE <plus-r #-}

  <trans : ∀ a b c
    → a < b ≡ tt
    → b < c ≡ tt
    → a < c ≡ tt
  <trans zero zero c p q = q
  <trans zero (pos x) zero p q = q
  <trans zero (pos x) (pos x₁) p q = refl
  <trans zero (pos x) (neg x₁) p q = q
  <trans zero (neg x) zero p q = p
  <trans zero (neg x) (pos x₁) p q = refl
  <trans zero (neg x) (neg x₁) p q = p
  <trans (pos x) zero zero p q = q
  <trans (pos x) zero (pos x₁) () q
  <trans (pos x) zero (neg x₁) () q
  <trans (pos x) (pos x₁) zero p q = q
  <trans (pos x) (pos x₁) (pos x₂) p q = <transⁿ x x₁ x₂ p q
  <trans (pos x) (pos x₁) (neg x₂) p q = q
  <trans (pos x) (neg x₁) zero p q = p
  <trans (pos x) (neg x₁) (pos x₂) () q
  <trans (pos x) (neg x₁) (neg x₂) p q = p
  <trans (neg x) zero zero p q = refl
  <trans (neg x) zero (pos x₁) p q = refl
  <trans (neg x) zero (neg x₁) p ()
  <trans (neg x) (pos x₁) zero p q = refl
  <trans (neg x) (pos x₁) (pos x₂) p q = refl
  <trans (neg x) (pos x₁) (neg x₂) p ()
  <trans (neg x) (neg x₁) zero p q = refl
  <trans (neg x) (neg x₁) (pos x₂) p q = refl
  <trans (neg x) (neg x₁) (neg x₂) p q = <transⁿ x₂ x₁ x q p

  <succpos : ∀ a
    → (zero < a) ≡ tt
    → (zero < succ a) ≡ tt
  <succpos zero p = refl
  <succpos (pos x) p = refl
  <succpos (neg x) ()

  <predneg : ∀ a
    → (a < zero) ≡ tt
    → (pred a < zero) ≡ tt
  <predneg zero p = refl
  <predneg (pos x) ()
  <predneg (neg x) p = refl

  <predpos : ∀ a
    → (zero < a) ≡ ff
    → (zero < pred a) ≡ ff
  <predpos zero p = refl
  <predpos (pos x) ()
  <predpos (neg x) p = refl

  <+Pos : ∀ a b
    → zero < a ≡ tt
    → zero < b ≡ tt
    → zero < a + b ≡ tt
  <+Pos zero b p q = q
  <+Pos (pos x) zero p q = refl
  <+Pos (pos x) (pos x₁) p q = refl
  <+Pos (pos x) (neg x₁) p ()
  <+Pos (neg x) b () q

  <+Neg : ∀ a b
    → a < zero ≡ tt
    → b < zero ≡ tt
    → a + b < zero ≡ tt
  <+Neg zero b () q
  <+Neg (pos x) b () q
  <+Neg (neg x) zero p ()
  <+Neg (neg x) (pos x₁) p ()
  <+Neg (neg x) (neg x₁) p q = refl

  <*Pos : ∀ a b
    → zero < a ≡ tt
    → zero < b ≡ tt
    → zero < a * b ≡ tt
  <*Pos zero b () q
  <*Pos (pos x) zero p ()
  <*Pos (pos x) (pos x₁) p q = refl
  <*Pos (pos x) (neg x₁) p ()
  <*Pos (neg x) b () q

  <posneg : ∀ a b
    → (a < zero) ≡ tt
    → (zero < b) ≡ tt
    → (a < b) ≡ tt
  <posneg a b = <trans a zero b


  -- <*posneg : ∀ a b → Prf (Pos a ~> Neg b ~> Neg (a * b))
  -- <*posneg zero b p q = p
  -- <*posneg (pos zeroⁿ) b p q = q
  -- <*posneg (pos (succⁿ x)) b p q = <+neg (pos x * b) b (<*posneg (pos x) b ** q) q
  -- <*posneg (neg x) b () q

  <*posn : ∀ n a b → (pos n * a) < (pos n * b) ≡ a < b
  <*posn zeroⁿ a b = refl
  <*posn (succⁿ n) zero zero = refl
  <*posn (succⁿ n) zero (pos x) = refl
  <*posn (succⁿ n) zero (neg x) = refl
  <*posn (succⁿ n) (pos x) zero = refl
  <*posn (succⁿ n) (pos x) (pos y) = <multⁿ (succⁿ x) (succⁿ y) (succⁿ n) 
  <*posn (succⁿ n) (pos x) (neg y) = refl
  <*posn (succⁿ n) (neg x) zero = refl
  <*posn (succⁿ n) (neg x) (pos y) = refl
  <*posn (succⁿ n) (neg x) (neg y) = <multⁿ (succⁿ y) (succⁿ x) (succⁿ n)
  {-# REWRITE <*posn #-}

  <*posn-r : ∀ n a b → (a * pos n) < (b * pos n) ≡ a < b
  <*posn-r zeroⁿ a b = refl
  <*posn-r (succⁿ n) zero zero = refl
  <*posn-r (succⁿ n) zero (pos x) = refl
  <*posn-r (succⁿ n) zero (neg x) = refl
  <*posn-r (succⁿ n) (pos x) zero = refl
  <*posn-r (succⁿ n) (pos x) (pos y) = <mult-r x y (succⁿ n)
  <*posn-r (succⁿ n) (pos x) (neg y) = refl
  <*posn-r (succⁿ n) (neg x) zero = refl
  <*posn-r (succⁿ n) (neg x) (pos y) = refl
  <*posn-r (succⁿ n) (neg x) (neg y) = <mult-r y x (succⁿ n)
  {-# REWRITE <*posn-r #-}

  <*Posn : ∀ z a b → Prf [ Pos z ] → Prf [ a < b ] → Prf [ z * a < z * b ]
  <*Posn zero a b p q = p
  <*Posn (pos x) a b p q = q
  <*Posn (neg x) a b () q

  <*Posn-r : ∀ z a b → Prf [ Pos z ] → Prf [ a < b ] → Prf [ a * z < b * z ]
  <*Posn-r zero a b () q
  <*Posn-r (pos x) a b p q = q
  <*Posn-r (neg x) a b () q

  <minus : ∀ a b → (- a) < (- b) ≡ (b < a)
  <minus zero b = refl
  <minus (pos x) zero = refl
  <minus (pos x) (pos y) = refl
  <minus (pos x) (neg y) = refl
  <minus (neg x) zero = refl
  <minus (neg x) (pos y) = refl
  <minus (neg x) (neg y) = refl
  {-# REWRITE <minus #-}  

  <*negn : ∀ n a b → (neg n * a) < (neg n * b) ≡ b < a
  <*negn zeroⁿ a b = refl
  <*negn (succⁿ n) a b = 
    begin
      - (pos (succⁿ n)) * a < - (pos (succⁿ n)) * b ≡⟨ refl ⟩
      - ((pos (succⁿ n)) * a) < - ((pos (succⁿ n)) * b) ≡⟨ <minus (pos (succⁿ n) * a) (pos (succⁿ n) * b) ⟩
      ((pos (succⁿ n)) * b) < ((pos (succⁿ n)) * a) ≡⟨ <*posn (succⁿ n) b a ⟩
      (b < a)
    qed
  {-# REWRITE <*negn #-}    

  <halfpos : (z : ℤ) → (p : even z ≡ tt) → zero < half z p ≡ zero < z
  <halfpos zero p = refl
  <halfpos (pos zeroⁿ) ()
  <halfpos (pos (succⁿ zeroⁿ)) p = refl
  <halfpos (pos (succⁿ (succⁿ x))) p = <succpos (half (pos x) p) (<halfpos (pos x) p)
  <halfpos (neg zeroⁿ) ()
  <halfpos (neg (succⁿ zeroⁿ)) p = refl
  <halfpos (neg (succⁿ (succⁿ x))) p = <predpos (half (neg x) p) (<halfpos (neg x) p)
  {-# REWRITE <halfpos #-}


  <succ-tt : ∀ z → z < succ z ≡ tt
  <succ-tt zero = refl
  <succ-tt (pos zeroⁿ) = refl
  <succ-tt (pos (succⁿ x)) = <succ-tt (pos x)
  <succ-tt (neg zeroⁿ) = refl
  <succ-tt (neg (succⁿ x)) = <succ-tt (pos x)
  {-# REWRITE <succ-tt #-}

  <pred-tt : ∀ z → pred z < z ≡ tt
  <pred-tt zero = refl
  <pred-tt (pos zeroⁿ) = refl
  <pred-tt (pos (succⁿ x)) = <pred-tt (neg x)
  <pred-tt (neg zeroⁿ) = refl
  <pred-tt (neg (succⁿ x)) = <pred-tt (neg x)
  {-# REWRITE <pred-tt #-}

  exp2pos : ∀ n → (zero < exp2 n) ≡ tt
  exp2pos zeroⁿ = refl
  exp2pos (succⁿ n) = <+Pos (exp2 n) (exp2 n) (exp2pos n) (exp2pos n)
  {-# REWRITE exp2pos #-}

  exp2pos' : ∀ n → exp2 n ≡ pos (exp2-1 n)
  exp2pos' zeroⁿ = refl
  exp2pos' (succⁿ n) = 
    begin
      exp2 n + exp2 n             ≡⟨ ap (_+ exp2 n) (exp2pos' n) ⟩
      pos (exp2-1 n) + exp2 n    ≡⟨ ap (pos (exp2-1 n) +_) (exp2pos' n) ⟩
      pos (exp2-1 n) + pos (exp2-1 n) ≡⟨ refl ⟩
      pos (succⁿ (exp2-1 n +ⁿ exp2-1 n)) ≡⟨ ap pos refl ⟩
      pos (succⁿ (exp2-1 n) +ⁿ exp2-1 n) ≡⟨ ap (λ u →  pos (u +ⁿ exp2-1 n)) (exp2succ n) ⟩
      pos (exp2n n +ⁿ exp2-1 n)
    qed
  {-# REWRITE exp2pos' #-}

  lemma-dist1 : ∀ a b c d → a + b < a + c + d ≡ b < c + d
  lemma-dist1 a b c d = 
    begin
      ((a + b) < (a + c + d)) ≡⟨ refl ⟩
      (a + b) < (a + (c + d)) ≡⟨ <plus a b (c + d) ⟩
      (b < (c + d))
    qed
  {-# REWRITE lemma-dist1 #-}

  lemma-comm1 : ∀ a b c d → (a + b < c + a + d) ≡ b < c + d
  lemma-comm1 a b c d = 
    begin
      (a + b < c + a + d) ≡⟨ ap (λ u → a + b < u + d) (+comm c a) ⟩
      (a + b < a + c + d) ≡⟨ refl ⟩
      b < c + d
    qed
  {-# REWRITE lemma-comm1 #-}

  lemma-comm2 : ∀ a b c d e → (a + b + c < d + a + e) ≡ b + c < d + e
  lemma-comm2 a b c d e = 
    begin
      ((a + b + c) < (d + a + e)) ≡⟨ ap (λ u → a + b + c < u + e) (+comm d a) ⟩
      ((a + (b + c)) < (a + (d + e))) ≡⟨ <plus a (b + c) (d + e) ⟩      
      ((b + c) < (d + e))
    qed
  {-# REWRITE lemma-comm2 #-}

  -- lemma-int3 : ∀ a b c d e → (a + (b + c) * d < d * a + e)
