{-# OPTIONS --without-K #-}

module Naturals where

open import Prop public
open import Base public
open import Booleans public
open import Equality public


data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}


succ-inj-l : ∀ n m → (n ≡ m) → (succ n ≡ succ m)
succ-inj-l n m p = ap succ p

succ-inj-r : ∀ n m → (succ n ≡ succ m) → (n ≡ m)
succ-inj-r n .n refl = refl

infixl 30 _+_
_+_ : ℕ → ℕ → ℕ
zero + b = b
succ a + b = succ (a + b)
{-# BUILTIN NATPLUS _+_ #-}

+rzero : ∀ n → n + 0 ≡ n
+rzero 0 = refl
+rzero (succ n) = ap succ (+rzero n)

+rone : ∀ n → n + 1 ≡ succ n
+rone zero = refl
+rone (succ n) = ap succ (+rone n)

+rsucc : ∀ n m → n + succ m ≡ succ (n + m)
+rsucc zero m = refl
+rsucc (succ n) m = ap succ (+rsucc n m)

+assoc : ∀ n m o → n + (m + o) ≡ n + m + o
+assoc zero m o = refl
+assoc (succ n) m o = ap succ (+assoc n m o)


+comm : ∀ n m → n + m ≡ m + n
+comm zero m rewrite +rzero m = refl
+comm (succ n) m rewrite +rsucc m n = ap succ (+comm n m)

+inj : ∀ a b c → a + b ≡ a + c → b ≡ c
+inj zero b c p = p
+inj (succ a) b c p = +inj a b c (succ-inj-r (a + b) (a + c) p)

+inj-r : ∀ b c a → b + a ≡ c + a → b ≡ c
+inj-r b c zero p rewrite +rzero b | +rzero c = p
+inj-r b c (succ a) p rewrite +rsucc b a | +rsucc c a = +inj-r b c a (succ-inj-r (b + a) (c + a) p)

-- Multiplication
infixl 35 _*_
_*_ : ℕ → ℕ → ℕ
zero * m = zero
succ n * m = m + (n * m)
{-# BUILTIN NATTIMES _*_ #-}


*rzero : ∀ n → n * zero ≡ zero
*rzero zero = refl
*rzero (succ n) = *rzero n

*runit : ∀ n → n * 1 ≡ n
*runit zero = refl
*runit (succ n) = ap succ (*runit n)

*rsucc : ∀ n m → n * succ m ≡ (n * m) + n
*rsucc zero m = refl
*rsucc (succ n) m rewrite
  (*rsucc n m)
  | +assoc m (n * m) n
  | +rsucc (n * m) n
  | +assoc m (n * m) (succ n)
  | inv (+assoc m (n * m) (succ n))
  | +rsucc (n * m) n
  | +rsucc m (n * m + n)
  | +assoc m (n * m) n
  = refl

*comm : ∀ n m → n * m ≡ m * n
*comm zero m rewrite (*rzero m) = refl
*comm (succ n) m rewrite
  +comm m (n * m)
  | *comm n m
  | inv (*rsucc m n)
  = refl

*distr : ∀ a b c → a * (b + c) ≡ a * b + a * c
*distr zero b c = refl
*distr (succ a) b c rewrite
  *distr a b c
  | +comm c (a * b)
  | inv (+assoc b c (a * b + a * c))
  | inv (+assoc b (a * b) (c + a * c))
  | +assoc c (a * b) (a * c)
  | +comm c (a * b)
  | +assoc (a * b) c (a * c)
  = refl

*distr-r : ∀ b c a → (b + c) * a ≡ b * a + c * a
*distr-r b c a rewrite *comm (b + c) a | *comm b a | *comm c a | *distr a b c = refl

*assoc : ∀ a b c → a * (b * c) ≡ a * b * c
*assoc zero b c = refl
*assoc (succ a) b c rewrite
  *assoc a b c
  | *distr-r b (a * b) c
  = refl

data Less (n m : ℕ) : Set where
  less : (k : ℕ) → succ (k + n) ≡ m → Less n m

data LessThan (n m : ℕ) : Set where
  lth : (k : ℕ) → k + n ≡ m → LessThan n m 

_==_ : ℕ → ℕ → Bool
zero  == zero  = true
zero  == succ _ = false
succ _ == zero = false
succ n == succ m = n == m
{-# BUILTIN NATEQUALS _==_ #-}

infix 6 _<_ 
_<_ : ℕ → ℕ → Bool
_ < zero = false
zero < succ _ = true
succ n < succ m = n < m
{-# BUILTIN NATLESS _<_ #-}

<evd : (n m : ℕ) → n < m ≡ true → Σ ℕ (λ k → (n + k ≡ m) × (0 < k ≡ true))
<evd zero zero ()
<evd zero (succ m) p = succ m , (refl , refl)
<evd (succ n) zero ()
<evd (succ n) (succ m) p with <evd n m p
<evd (succ n) (succ m) p | k , (α , β) = k , ((ap succ α) , β)

<zero : ∀ n → 0 < n ≡ false → n ≡ 0
<zero zero p = refl
<zero (succ n) ()

infix 6 _≤_ 
_≤_ : (n m : ℕ) → Bool
zero ≤ m = true
succ n ≤ zero = false
succ n ≤ succ m = n ≤ m

<not : ∀ n m → (n ≤ m) ≡ not (m < n)
<not zero zero = refl
<not zero (succ m) = refl
<not (succ n) zero = refl
<not (succ n) (succ m) = <not n m

≤not : ∀ n m → (n < m) ≡ not (m ≤ n)
≤not n m = not-inj (n < m) (not (m ≤ n)) lemma
  where
    lemma : not (n < m) ≡ not (not (m ≤ n))
    lemma rewrite not-double (m ≤ n) | <not m n = refl

<plus : ∀ k n m → (k + n < k + m) ≡ (n < m)
<plus zero n m = refl
<plus (succ k) n m = <plus k n m

<plus-r : ∀ k n m → (n + k < m + k) ≡ (n < m)
<plus-r zero n m rewrite +rzero n | +rzero m = refl
<plus-r (succ k) n m rewrite +rsucc n k | +rsucc m k | <plus-r k n m = refl

≤plus : ∀ k n m → (k + n ≤ k + m) ≡ (n ≤ m)
≤plus k n m rewrite <not (k + n) (k + m) | <not n m | <plus k m n = refl

≤plus-r : ∀ k n m → (n + k ≤ m + k) ≡ (n ≤ m)
≤plus-r k n m rewrite <not (n + k) (m + k) | <not n m | <plus-r k m n = refl


<trans : ∀ n m k
  → (n < m) ≡ true
  → (m < k) ≡ true
  → (n < k) ≡ true
<trans zero zero k p q = q
<trans zero (succ m) zero p q = q
<trans zero (succ m) (succ k) p q = refl
<trans (succ n) zero zero p q = q
<trans (succ n) zero (succ k) () q
<trans (succ n) (succ m) zero p q = q
<trans (succ n) (succ m) (succ k) p q = <trans n m k p q

≤trans : ∀ n m k
  → (n ≤ m) ≡ true
  → (m ≤ k) ≡ true
  → (n ≤ k) ≡ true
≤trans zero zero k p q = refl
≤trans zero (succ m) k p q = refl
≤trans (succ n) zero k () q
≤trans (succ n) (succ m) zero p ()
≤trans (succ n) (succ m) (succ k) p q = ≤trans n m k p q

<mult : ∀ n m k → (succ k * n < succ k * m) ≡ (n < m)
<mult n m zero rewrite +rzero n | +rzero m = refl
<mult n m (succ k) with (n < m)??
<mult n m (succ k) | inl f rewrite f =
  <trans (n + (n + k * n)) (n + (m + k * m)) (m + (m + k * m))
  lemma1 lemma2
  where
    lemma1 : n + (n + k * n) < n + (m + k * m) ≡ true
    lemma1 rewrite <plus n (succ k * n) (succ k * m) | <mult n m k | f = refl
    lemma2 : n + (m + k * m) < m + (m + k * m) ≡ true
    lemma2 rewrite <plus-r (m + k * m) n m | f = refl
<mult n m (succ k) | inr f rewrite f | ≤not (n + (n + k * n)) (m + (m + k * m)) = ap not (
  ≤trans (m + (m + k * m)) (m + (n + k * n)) (n + (n + k * n))
  lemma1 lemma2)
  where
    lemma1 : m + (m + k * m) ≤ m + (n + k * n) ≡ true
    lemma1 rewrite ≤plus m (m + k * m) (n + k * n) | <not (succ k * m) (succ k * n) = ap not (<mult n m k · f)
    lemma2 : m + (n + k * n) ≤ n + (n + k * n) ≡ true
    lemma2 rewrite ≤plus-r (n + k * n) m n | <not m n = ap not f


odd : (n : ℕ) → Bool
odd zero = false
odd (succ zero) = true
odd (succ (succ n)) = odd n

even : (n : ℕ) → Bool
even n = not (odd n)

oddsucc : (n : ℕ) → odd (succ n) ≡ not (odd n)
oddsucc zero = refl
oddsucc (succ zero) = refl
oddsucc (succ (succ n)) = oddsucc n

oddplus : (n m : ℕ) → odd (n + m) ≡ xor (odd n) (odd m)
oddplus zero m = refl
oddplus (succ n) m rewrite
  oddsucc n
  | oddsucc (n + m)
  | xor-not-l (odd n) (odd m)
  | oddplus n m
  = refl

odd+both : ∀ b → odd (b + b) ≡ false
odd+both zero = refl
odd+both (succ zero) = refl
odd+both (succ (succ b)) rewrite
  +rsucc b (succ b)
  | +rsucc b b
  | odd+both b
  = refl

oddmul : ∀ n m → odd (n * m) ≡ and (odd n) (odd m)
oddmul zero m = refl
oddmul (succ zero) m rewrite +rzero m = refl
oddmul (succ (succ n)) m rewrite
  oddplus m (m + n * m)
  | oddplus m (m + n * m)
  | oddplus m (n * m)
  | xor-assoc (odd m) (odd m) (odd (n * m))
  | xoraa (odd m)
  | oddmul n m
  = refl


evenplus : (n m : ℕ) → even (n + m) ≡ not (xor (even n) (even m))
evenplus n m rewrite
  xor-not-l (odd n) (not (odd m))
  | xor-not-r (odd n) (odd m)
  | not-double (xor (odd n) (odd m))
  | oddplus n m
  = refl

iszero : (n : ℕ) → Bool
iszero zero = true
iszero (succ n) = false

iszero-sound : (n : ℕ) → iszero n ≡ true → n ≡ 0
iszero-sound zero p = refl
iszero-sound (succ n) ()

iszero-plus : ∀ a b → and (iszero a) (iszero b) ≡ iszero (a + b)
iszero-plus zero b = refl
iszero-plus (succ a) b = refl

iszero-not-plus-r : ∀ a b
  → iszero a ≡ false
  -------------------------
  → iszero (a + b) ≡ false
iszero-not-plus-r zero b ()
iszero-not-plus-r (succ a) b p = refl

iszero-not-mult : ∀ a b
  → iszero a ≡ false
  → iszero b ≡ false
  --------------------
  → iszero (a * b) ≡ false
iszero-not-mult zero b () q
iszero-not-mult (succ a) zero p ()
iszero-not-mult (succ a) (succ b) p q = refl  

<mult-inj : ∀ n m k → iszero k ≡ false → k * n < k * m ≡ n < m
<mult-inj n m zero ()
<mult-inj n m (succ k) p = <mult n m k


not-odd-form : (n : ℕ) → odd n ≡ false → Σ ℕ (λ k → n ≡ k + k)
not-odd-form zero x = zero , refl
not-odd-form (succ zero) ()
not-odd-form (succ (succ n)) x with not-odd-form n x
not-odd-form (succ (succ n)) x | k , q rewrite q | inv (+rsucc k k) = (succ k) , refl

notodda+a : ∀ a → not (odd (a + a)) ≡ true
notodda+a a rewrite oddplus a a | xoraa (odd a) = refl

odda+a : ∀ a → odd (a + a) ≡ false
odda+a a rewrite
  inv (not-double (odd (a + a)))
  | notodda+a a
  = refl

notodd*a+b : ∀ a b → odd (a * (b + b)) ≡ false
notodd*a+b a b rewrite
  oddmul a (b + b)
  | odda+a b
  | and-false (odd a)
  = refl

exp2 : ℕ → ℕ
exp2 zero = 1
exp2 (succ n) = exp2 n + exp2 n

exp2plus : ∀ a b → exp2 (a + b) ≡ exp2 a * exp2 b
exp2plus zero b rewrite +rzero (exp2 b) = refl
exp2plus (succ a) b rewrite
  exp2plus a b
  | *comm (exp2 a + exp2 a) (exp2 b)
  | *distr (exp2 b) (exp2 a) (exp2 a)
  | *comm (exp2 a) (exp2 b)
  = refl

exp2-even : (n : ℕ) → iszero n ≡ false → even (exp2 n) ≡ true
exp2-even zero ()
exp2-even (succ n) p rewrite
  evenplus (exp2 n) (exp2 n)
  | xor-not-l (odd (exp2 n)) (not (odd (exp2 n)))
  | xor-not-r (odd (exp2 n)) (odd (exp2 n))
  | not-double (not (xor (odd (exp2 n)) (odd (exp2 n))))
  | inv (oddplus (exp2 n) (exp2 n))
  | notodda+a (exp2 n)
  = refl

exp2-notzero : (n : ℕ) → iszero (exp2 n) ≡ false
exp2-notzero zero = refl
exp2-notzero (succ n) = iszero-not-plus-r (exp2 n) (exp2 n) (exp2-notzero n)

a+a≡2a : ∀ a →
  a + a ≡ 2 * a
a+a≡2a zero = refl
a+a≡2a (succ a) rewrite
  +rsucc a a
  | +rzero a
  | +rsucc a a
  | a+a≡2a a
  = refl

a+a≡b+b : ∀ a b → a + a ≡ b + b → a ≡ b
a+a≡b+b zero zero = λ _ → refl
a+a≡b+b zero (succ b) = λ ()
a+a≡b+b (succ a) zero = λ ()
a+a≡b+b (succ a) (succ b) p rewrite
  +rsucc a a
  | +rsucc b b
  | a+a≡b+b a b (succ-inj-r (a + a) (b + b) (succ-inj-r (succ (a + a)) (succ (b + b)) p))
  = refl

a*b≡0 : ∀ a b
  → a * b ≡ 0
  -----------------------
  → (a ≡ 0) ⊎ (b ≡ 0)
a*b≡0 zero b p = inl refl
a*b≡0 (succ a) zero p = inr refl
a*b≡0 (succ a) (succ b) ()

0≡a*nz : ∀ a b
  → a * b ≡ 0
  → iszero b ≡ false
  ---------------------
  → a ≡ 0
0≡a*nz zero b p q = refl
0≡a*nz (succ a) zero p ()
0≡a*nz (succ a) (succ b) () q

0≡a+b→0≡a : ∀ a b → 0 ≡ a + b → 0 ≡ a
0≡a+b→0≡a zero b = λ _ → refl
0≡a+b→0≡a (succ a) b = λ ()

*inj : ∀ a b c
  → iszero a ≡ false
  → a * b ≡ a * c
  -------------------
  → b ≡ c
*inj zero b c () q
*inj (succ a) zero c p q rewrite *rzero a = 0≡a+b→0≡a c (a * c) q
*inj (succ a) (succ b) zero p q rewrite *rzero a = inv (0≡a+b→0≡a (succ b) (a * succ b) (inv q))
*inj (succ a) (succ b) (succ c) p q rewrite
  *rsucc a b
  | *rsucc a c
  | +assoc b (a * b) a
  | +assoc c (a * c) a
  = ap succ (*inj (succ a) b c p lemma2)
  where
    lemma1 : (b + a * b) + a ≡ (c + a * c) + a
    lemma1 = succ-inj-r (b + a * b + a) (c + a * c + a) q 
    lemma2 : b + a * b ≡ c + a * c
    lemma2 = +inj-r (b + a * b) (c + a * c) a lemma1



*cancel : ∀ a b c
  → b ≡ c
  -------------------
  → a * b ≡ a * c
*cancel a b .b refl = refl



simpl-a2b≡c2d : ∀ a b c d
  → a * (b + b) ≡ c * (d + d)
  ----------------------------
  → a * b ≡ c * d
simpl-a2b≡c2d a b c d rewrite
  *distr a b b
  | *distr c d d
  | a+a≡2a (a * b)
  | a+a≡2a (c * d)
  = *inj 2 (a * b) (c * d) refl


exp2-odd-div : ∀ n m e d
  → odd n ≡ true
  → odd m ≡ true
  → n * exp2 e ≡ m * exp2 d
  --------------------------
  → n ≡ m
exp2-odd-div n m zero zero x y p rewrite *runit n | *runit m = p
exp2-odd-div n m zero (succ d) x y p rewrite
  *runit n
  | p
  | oddmul m (exp2 d + exp2 d)
  | odd+both (exp2 d)
  | and-false (odd m)
  = refute (inv x)
  where
    refute : true ≡ false → m * (exp2 d + exp2 d) ≡ m
    refute ()
exp2-odd-div n m (succ e) zero x y p rewrite
  *runit m
  | inv p
  | oddmul n (exp2 e + exp2 e)
  | odd+both (exp2 e)
  | x
  = refute y
  where
    refute : {A : Set} → false ≡ true → A
    refute ()
exp2-odd-div n m (succ e) (succ d) x y p
  = exp2-odd-div n m e d x y (simpl-a2b≡c2d n (exp2 e) m (exp2 d) p)

zero≢succ : ∀ a → 0 ≡ succ a → ⊥
zero≢succ a = λ ()


exp2-inj : ∀ a b → exp2 a ≡ exp2 b → a ≡ b
exp2-inj zero zero p = refl
exp2-inj zero (succ b) p with (exp2 b)
exp2-inj zero (succ b) () | zero
exp2-inj zero (succ b) p | succ w with (succ-inj-r zero (w + succ w) p)
... | v rewrite +rsucc w w = exfalso (zero≢succ (w + w) v)
exp2-inj (succ a) zero p with (exp2 a)
exp2-inj (succ a) zero () | zero
exp2-inj (succ a) zero p | succ w with (succ-inj-r (w + succ w) zero p)
... | v rewrite +rsucc w w = exfalso (zero≢succ (w + w) (inv v))
exp2-inj (succ a) (succ b) p = ap succ (exp2-inj a b (lemma (exp2 a) (exp2 b) p))
  where
    lemma : ∀ a b → a + a ≡ b + b → a ≡ b
    lemma zero zero = λ _ → refl
    lemma zero (succ b) = λ ()
    lemma (succ a) zero = λ ()
    lemma (succ a) (succ b) p rewrite +rsucc a a | +rsucc b b =
      ap succ (lemma a b (succ-inj-r _ _ (succ-inj-r (succ (a + a)) (succ (b + b)) p)))

*cross : ∀ a b c d e f
  → iszero c ≡ false
  → a * d ≡ c * b
  → c * f ≡ e * d
  -------------------
  → a * f ≡ e * b
*cross a b c d e f x p q = *inj c (a * f) (e * b) x lemma
  where
    lemma : c * (a * f) ≡ c * (e * b)
    lemma rewrite
      *comm a f
      | *assoc c f a
      | q
      | inv (*assoc e d a)
      | *comm d a
      | p
      | *assoc e c b
      | *comm e c
      | *assoc c e b
      = refl

*bicross : ∀ a b c d e f g h
  → iszero c ≡ false
  → iszero e ≡ false
  → a * d ≡ c * b
  → c * f ≡ e * d
  → e * h ≡ g * f
  -----------------------------
  → a * h ≡ g * b
*bicross a b c d e f g h x y p q r = *cross a b e f g h y (*cross a b c d e f x p q) r


ndec≡ : (a b : ℕ) → (a ≡ b) ⊎ ¬ (a ≡ b)
ndec≡ zero zero = inl refl
ndec≡ zero (succ b) = inr (λ ())
ndec≡ (succ a) zero = inr (λ ())
ndec≡ (succ a) (succ b) with ndec≡ a b
ndec≡ (succ a) (succ b) | inl x = inl (ap succ x)
ndec≡ (succ a) (succ b) | inr x = inr λ x₁ → x (succ-inj-r a b x₁)
