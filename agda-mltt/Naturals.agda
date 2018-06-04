{-# OPTIONS --without-K #-}

-- Agda-MLTT library.
-- Author: Mario Román.

-- Naturals.  Natural numbers, addition, multiplication, ordering and
-- properties and lemmas over these definitions. A binary exponential
-- function is considered (it will be useful when defining Dyadic
-- numbers) and an integral square root is also considered.


module Naturals where

open import Prop public
open import Base public
open import Booleans public
open import Equality public


-- Definition of the natural numbers as an initial algebra over a
-- polynomial endofunctor. They are described as an inductive type
-- with two constructors representing Peano notation.
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}


-- Succesor is injective.
succ-inj-l : ∀ n m → (n ≡ m) → (succ n ≡ succ m)
succ-inj-l n m = ap succ

succ-inj-r : ∀ n m → (succ n ≡ succ m) → (n ≡ m)
succ-inj-r n .n refl = refl

-- Inductive definition of addition.
infixl 30 _+_
_+_ : ℕ → ℕ → ℕ
zero + b = b
succ a + b = succ (a + b)
{-# BUILTIN NATPLUS _+_ #-}

-- Some lemmas on addition of natural numbers. We prove them using the
-- properties of the equality types and the induction principle for
-- natural numbers.
+rzero : ∀ n → n + 0 ≡ n
+rzero 0 = refl
+rzero (succ n) = ap succ (+rzero n)

+rone : ∀ n → n + 1 ≡ succ n
+rone zero = refl
+rone (succ n) = ap succ (+rone n)

+rsucc : ∀ n m → n + succ m ≡ succ (n + m)
+rsucc zero m = refl
+rsucc (succ n) m = ap succ (+rsucc n m)

-- Associativity.
+assoc : ∀ n m o → n + (m + o) ≡ n + m + o
+assoc zero m o = refl
+assoc (succ n) m o = ap succ (+assoc n m o)

-- Commutativity.
+comm : ∀ n m → n + m ≡ m + n
+comm zero m rewrite +rzero m = refl
+comm (succ n) m rewrite +rsucc m n = ap succ (+comm n m)

-- Left cancellation.
+inj : ∀ a b c → a + b ≡ a + c → b ≡ c
+inj zero b c p = p
+inj (succ a) b c p = +inj a b c (succ-inj-r (a + b) (a + c) p)

-- Right cancellation.
+inj-r : ∀ b c a → b + a ≡ c + a → b ≡ c
+inj-r b c zero p rewrite +rzero b | +rzero c = p
+inj-r b c (succ a) p rewrite +rsucc b a | +rsucc c a = +inj-r b c a (succ-inj-r (b + a) (c + a) p)


-- Inductive definition of multiplication.
infixl 35 _*_
_*_ : ℕ → ℕ → ℕ
zero * m = zero
succ n * m = m + (n * m)
{-# BUILTIN NATTIMES _*_ #-}


-- Some lemmas on the multiplication operation.
*rzero : ∀ n → n * zero ≡ zero
*rzero zero = refl
*rzero (succ n) = *rzero n

*runit : ∀ n → n * 1 ≡ n
*runit zero = refl
*runit (succ n) = ap succ (*runit n)

*rsucc : ∀ n m → n * succ m ≡ (n * m) + n
*rsucc zero m = refl
*rsucc (succ n) m rewrite
  *rsucc n m
  | +assoc m (n * m) n
  | +rsucc (n * m) n
  | +assoc m (n * m) (succ n)
  | inv (+assoc m (n * m) (succ n))
  | +rsucc (n * m) n
  | +rsucc m (n * m + n)
  | +assoc m (n * m) n
  = refl

-- Commutativity.
*comm : ∀ n m → n * m ≡ m * n
*comm zero m rewrite (*rzero m) = refl
*comm (succ n) m rewrite
  +comm m (n * m)
  | *comm n m
  | inv (*rsucc m n)
  = refl

-- Left-distributivity over addition.
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

-- Right-distributivity over addition.
*distr-r : ∀ b c a → (b + c) * a ≡ b * a + c * a
*distr-r b c a rewrite
  *comm (b + c) a
  | *comm b a
  | *comm c a
  | *distr a b c
  = refl

-- Associativity.
*assoc : ∀ a b c → a * (b * c) ≡ a * b * c
*assoc zero b c = refl
*assoc (succ a) b c rewrite
  *assoc a b c
  | *distr-r b (a * b) c
  = refl


-- Definition of a 'strictly less than' relation as an inductively
-- constructed type. The definition of a 'less or equal than' relation
-- follows the same pattern. They both depend on addition.
data Less (n m : ℕ) : Set where
  less : (k : ℕ) → succ (k + n) ≡ m → Less n m

data LessThan (n m : ℕ) : Set where
  lth : (k : ℕ) → k + n ≡ m → LessThan n m 

-- Equality for natural numbers is decidable by induction. That is,
-- any two numbers are equal or distinct; we have excluded middle for
-- this particular case.
_==_ : ℕ → ℕ → Bool
zero  == zero  = true
zero  == succ _ = false
succ _ == zero = false
succ n == succ m = n == m
{-# BUILTIN NATEQUALS _==_ #-}

-- The less-than relation is decidable by induction.
infix 6 _<_ 
_<_ : ℕ → ℕ → Bool
_ < zero = false
zero < succ _ = true
succ n < succ m = n < m
{-# BUILTIN NATLESS _<_ #-}


-- A function that extracts evidence from the fact that a number is
-- smaller than other. A function extracting the same evidence for a
-- 'less or equal than' relation is presented.
<evd : (n m : ℕ) → n < m ≡ true → Σ ℕ (λ k → (n + k ≡ m) × (0 < k ≡ true))
<evd zero zero ()
<evd zero (succ m) p = succ m , (refl , refl)
<evd (succ n) zero ()
<evd (succ n) (succ m) p with <evd n m p
... | k , (α , β) = k , ((ap succ α) , β)

<nevd : (n m : ℕ) → n < m ≡ false → Σ ℕ (λ k → m + k ≡ n)
<nevd zero zero p = 0 , refl
<nevd zero (succ m) ()
<nevd (succ n) zero p = succ n , refl
<nevd (succ n) (succ m) p with <nevd n m p
... | k , α = k , succ-inj-l (m + k) n α

-- No natural number is less than zero.
<zero : ∀ n → 0 < n ≡ false → n ≡ 0
<zero zero p = refl
<zero (succ n) ()

-- A less than relation defined as a function on the natural numbers.
infix 6 _≤_ 
_≤_ : (n m : ℕ) → Bool
zero ≤ m = true
succ n ≤ zero = false
succ n ≤ succ m = n ≤ m

-- Some lemmas on natural number ordering.
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

-- Ordering preserves addition.
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


-- Transitivty of the 'less than' relation.
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

-- Transitivty of the 'less or equal than' relation.
≤trans : ∀ n m k
  → (n ≤ m) ≡ true
  → (m ≤ k) ≡ true
  → (n ≤ k) ≡ true
≤trans zero zero k p q = refl
≤trans zero (succ m) k p q = refl
≤trans (succ n) zero k () q
≤trans (succ n) (succ m) zero p ()
≤trans (succ n) (succ m) (succ k) p q = ≤trans n m k p q


-- Multiplication (by a number different from zero) preserves ordering.
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


-- Parity of natural numbers.
odd : (n : ℕ) → Bool
odd zero = false
odd (succ zero) = true
odd (succ (succ n)) = odd n

even : (n : ℕ) → Bool
even n = not (odd n)

-- Lemmas on parity.
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


-- A decidable predicate that is true if and only if the natural
-- number is zero. This is useful as an argument to proofs that
-- require the number not to be zero.
iszero : (n : ℕ) → Bool
iszero zero = true
iszero (succ n) = false

-- Lemmas on being zero.
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

<iszero : ∀ n → 0 < n ≡ true → iszero n ≡ false
<iszero zero = λ ()
<iszero (succ n) = λ _ → refl

iszero< : ∀ n → iszero n ≡ false → 0 < n ≡ true
iszero< zero ()
iszero< (succ n) p = refl

zero<false : ∀ n → zero < n ≡ false → n ≡ 0
zero<false zero = λ _ → refl
zero<false (succ n) = λ ()


-- A version of the previous lemma using the 'iszero' predicate.
<mult-inj : ∀ n m k → iszero k ≡ false → k * n < k * m ≡ n < m
<mult-inj n m zero ()
<mult-inj n m (succ k) p = <mult n m k

-- Extracting evidence from the fact that a number is even. If n is
-- even, it has to be of the form (n = k + k) for some k.
not-odd-form : (n : ℕ) → odd n ≡ false → Σ ℕ (λ k → n ≡ k + k)
not-odd-form zero x = zero , refl
not-odd-form (succ zero) ()
not-odd-form (succ (succ n)) x with not-odd-form n x
not-odd-form (succ (succ n)) x | k , q rewrite q | inv (+rsucc k k) = (succ k) , refl

-- More lemmas on parity of natural numbers.
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


-- Binary exponentiation of natural numbers. This operation is crucial
-- on the definition of the Dyadic rational numbers.
exp2 : ℕ → ℕ
exp2 zero = 1
exp2 (succ n) = exp2 n + exp2 n

-- Lemmas on binary exponentiation.
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

<bound+ : ∀ a b c → a < b ≡ true → a < b + c ≡ true
<bound+ a b zero p rewrite +rzero b = p
<bound+ a b (succ c) p rewrite +rsucc b c = <trans a (b + c) (succ (b + c)) (<bound+ a b c p) (v (b + c))
  where
    v : ∀ a → a < succ a ≡ true
    v zero = refl
    v (succ a) = v a

<bound* : ∀ a b c → 0 < c ≡ true → a < b ≡ true → a < b * c ≡ true
<bound* a b zero ()
<bound* a b (succ c) p q rewrite *rsucc b c | +comm (b * c) b = <bound+ a b (b * c) q

<boundsucc : ∀ a b → a < b ≡ true → a < succ b ≡ true
<boundsucc a b p rewrite inv (+rone b) = <bound+ a b 1 p

<boundpred : ∀ a b → succ a < b ≡ true → a < b ≡ true
<boundpred a zero p = p
<boundpred a (succ b) p = <boundsucc a b p

exp2>zero : (n : ℕ) → 0 < exp2 n ≡ true
exp2>zero zero = refl
exp2>zero (succ n) = <bound+ zero (exp2 n) (exp2 n) (exp2>zero n)

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

-- Multiplication, by a nonzero number, is injective.
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


eq≤ : ∀ a b → a ≡ b → b < a ≡ false
eq≤ zero .0 refl = refl
eq≤ (succ a) .(succ a) refl = eq≤ a a refl

eq≤succ : ∀ a b
  → b < a ≡ false
  → succ b < a ≡ false
eq≤succ zero b p = refl
eq≤succ (succ a) zero ()
eq≤succ (succ a) (succ b) p = eq≤succ a b p

eq< : ∀ a b
  → a < succ b ≡ true
  → ¬ (a ≡ b)
  → a < b ≡ true
eq< zero zero refl q = exfalso (q refl)
eq< zero (succ b) p q = refl
eq< (succ a) zero () q
eq< (succ a) (succ b) p q = eq< a b p λ x → q (ap succ x)

<succ : ∀ a → a < succ a ≡ true
<succ zero = refl
<succ (succ a) = <succ a

-- Squares and truncated square root
_² : ℕ → ℕ
n ² = n * n

-- A 'natural square root' that provides bounds to the real value of
-- the square root of a number.
nsqr : ℕ → ℕ
nsqr zero = zero
nsqr (succ n) with ndec≡ (succ (nsqr n) * succ (nsqr n)) (succ n)
nsqr (succ n) | inl x = succ (nsqr n)
nsqr (succ n) | inr x = nsqr n

nsqr-lbound : (n : ℕ) → n < (nsqr n)² ≡ false
nsqr-lbound zero = refl
nsqr-lbound (succ n) with ndec≡ (succ (nsqr n) * succ (nsqr n)) (succ n)
nsqr-lbound (succ n) | inl x = eq≤ _ n (succ-inj-r _ _ x)
nsqr-lbound (succ n) | inr x = eq≤succ (nsqr n * nsqr n) n (nsqr-lbound n)

nsqr-iszero : ∀ n → iszero n ≡ iszero (nsqr n)
nsqr-iszero zero = refl
nsqr-iszero (succ n) with ndec≡ (succ (nsqr n) * succ (nsqr n)) (succ n)
nsqr-iszero (succ n) | inl x = refl
nsqr-iszero (succ n) | inr x rewrite inv (nsqr-iszero n) with (iszero n)??
... | inl x₁ rewrite (iszero-sound n x₁) = exfalso (x refl)
... | inr x₁ = inv x₁

nsqr-ubound : (n : ℕ) → n < (succ (nsqr n))² ≡ true
nsqr-ubound zero = refl
nsqr-ubound (succ n) with ndec≡ (succ (nsqr n) * succ (nsqr n)) (succ n)
nsqr-ubound (succ n) | inl x with nsqr-ubound n
... | w = <trans n (succ (nsqr n + nsqr n * succ (nsqr n)))
  (succ (nsqr n + succ (succ (nsqr n + nsqr n * succ (succ (nsqr n))))))
  w
  (lemma n)
  where
    lemma : ∀ n →
      nsqr n + nsqr n * succ (nsqr n) <
      nsqr n + succ (succ (nsqr n + nsqr n * succ (succ (nsqr n))))
      ≡ true
    lemma zero = refl
    lemma (succ m) rewrite
      <plus (nsqr (succ m))
        (nsqr (succ m) * succ (nsqr (succ m)))
          (succ (succ (nsqr (succ m) + nsqr (succ m) * succ (succ (nsqr (succ m))))))
      = <boundsucc (nsqr (succ m) * succ (nsqr (succ m)))
         (succ (nsqr (succ m) + nsqr (succ m) * succ (succ (nsqr (succ m)))))
        (<boundsucc (nsqr (succ m) * succ (nsqr (succ m)))
          (nsqr (succ m) + nsqr (succ m) * succ (succ (nsqr (succ m))))
        (lemma2 (succ m) refl))
      where
        lemma2 : ∀ n → iszero n ≡ false →
          nsqr n * succ (nsqr n) <
          nsqr n + nsqr n * succ (succ (nsqr n))
          ≡ true
        lemma2 n p rewrite
          +comm (nsqr n) (nsqr n * succ (succ (nsqr n)))
          = <bound+ (nsqr n * succ (nsqr n)) (nsqr n * succ (succ (nsqr n))) (nsqr n)
            lemma3
          where
            lemma3 : nsqr n * succ (nsqr n) < nsqr n * succ (succ (nsqr n)) ≡ true
            lemma3 rewrite
              <mult-inj (succ (nsqr n)) (succ (succ (nsqr n))) (nsqr n) ((inv (nsqr-iszero n)) · p)
              = <succ (nsqr n)
nsqr-ubound (succ n) | inr x = eq< n
  (nsqr n + nsqr n * succ (nsqr n)) (nsqr-ubound n) λ x₁ → x (inv (ap succ x₁))

-- A lemma on addition and ordering that eases future proofs.
<+< : ∀ a b c d
  → a < b ≡ true
  → c < d ≡ true
  → a + c < b + d ≡ true
<+< zero b c d p q rewrite +comm b d = <bound+ c d b q
<+< (succ a) b zero d p q rewrite +rzero a = <bound+ (succ a) b d p
<+< (succ a) zero (succ c) d () q
<+< (succ a) (succ b) (succ c) zero p ()
<+< (succ a) (succ b) (succ c) (succ d) p q = <+< a b (succ c) (succ d) p q


-- Squares preserve ordering.
<sq : ∀ a b
  → a < b ≡ true
  → a ² < b ² ≡ true
<sq zero zero p = p
<sq zero (succ b) p = refl
<sq (succ a) zero p = p
<sq (succ a) (succ b) p rewrite
  *comm a (succ a)
  | *comm b (succ b)
  = <+< a b (a + a * a) (b + b * b) p
    (<+< a b (a * a) (b * b) p
    (<sq a b p))

sq-space : (u a : ℕ)
  →  a ² < u ² ≡ false
  →  a < u ≡ true
  → ⊥
sq-space zero a refl ()
sq-space (succ u) a p q = true≢false (inv (<sq a (succ u) q) · p)


eq<n : ∀ a b → a ≡ b → a < b ≡ false
eq<n zero .0 refl = refl
eq<n (succ a) .(succ a) refl = eq<n a a refl


-- Given two numbers x,y such that (2a+1 < y-x), and (y < a²) we can
-- find an square between them.
sqrbetween : (x y a k : ℕ)
  → x + k ≡ y
  → succ (a + a) < k ≡ true
  → y < a ² ≡ true
  → Σ ℕ (λ c → (x < c ² ≡ true) × (y < c ² ≡ false))
sqrbetween x y zero k p q ()
sqrbetween x y (succ a) k p q r with (y < a ²)??
... | inl w = sqrbetween x y a k p lemma w
  where
    lemma : succ (a + a) < k ≡ true
    lemma rewrite +rsucc a a = <boundpred (succ (a + a)) k (<boundpred (succ (succ (a + a))) k q)
... | inr w with (x < a ²)??
... | inl v = a , (v , w)
... | inr v with (<nevd x (a ²) v)
... | (l , α) rewrite (inv p) | inv α = exfalso
  (true≢false (inv lemma2 · eq<n (a * a + 2 * a + 1) (succ a * succ a) (lemma3 a)))
  where
    lemma : a * a + l + 2 * a + 1 < succ (a + a * succ a) ≡ true
    lemma = <trans (a * a + l + 2 * a + 1) (a * a + l + k)
              (succ (a + a * succ a))
              sublem
              r 
      where
        sublem : a * a + l + (a + (a + zero)) + 1 < a * a + l + k ≡ true
        sublem rewrite
          inv (+assoc ((a * a) + l) (a + (a + zero)) 1)
          | <plus ((a * a) + l) ((a + (a + zero)) + 1) k
          | +rone (a + (a + 0))
          | +rzero a
          | +rsucc a a
          = <boundpred (succ (a + a)) k (<boundpred (succ (succ (a + a))) k q)

    lemma2 : a * a + 2 * a + 1 < succ a * succ a ≡ true
    lemma2 with <evd (a * a + l + (a + (a + zero)) + 1) (succ (a + a * succ a)) lemma
    ... | (j , (β , γ)) rewrite
      inv β
      | inv (+assoc (a * a) l (a + (a + 0)))
      | +rzero a
      | +comm l (a + a)
      | inv (+assoc (a * a) (a + a + l) 1)
      | inv (+assoc (a * a) (a + a + l + 1) j)
      | inv (+assoc (a * a) (a + a) 1)
      | <plus (a * a) (a + a + 1) (a + a + l + 1 + j)
      | inv (+assoc ((a + a) + l) 1 j)
      | inv (+assoc (a + a) l (succ j))
      | <plus (a + a) 1 (l + succ j)
      | +rsucc l j
      | +comm l j
      = <bound+ zero j l γ

    lemma3 : ∀ a → a * a + 2 * a + 1 ≡ succ a * succ a
    lemma3 a rewrite
      *distr (succ a) 1 a
      | *runit a
      | +rzero a
      | +comm (a * a + (a + a)) 1
      | +comm (a * a) (a + a)
      | +assoc a a (a * a)
      = refl

-- Any number a is less than 2ᵃ.
a<exp2a : ∀ a → a < exp2 a ≡ true
a<exp2a zero = refl
a<exp2a (succ a) with a<exp2a a
a<exp2a (succ zero) | w = refl
a<exp2a (succ (succ a)) | w =
  <trans (succ (succ a)) (succ (exp2 a + exp2 a)) (exp2 a + exp2 a + (exp2 a + exp2 a))
    w lemma
    where
      lemma2 : ∀ a → 1 < exp2 a + exp2 a ≡ true
      lemma2 zero = refl
      lemma2 (succ a) = <bound+ 1 (exp2 a + exp2 a) (exp2 a + exp2 a) (lemma2 a)
      lemma : succ (exp2 a + exp2 a) < exp2 a + exp2 a + (exp2 a + exp2 a) ≡ true
      lemma rewrite
        +comm 1 (exp2 a + exp2 a)
        | <plus (exp2 a + exp2 a) 1 (exp2 a + exp2 a)
        = lemma2 a

dexp : ∀ n → 1 < exp2 n + exp2 n ≡ true
dexp zero = refl
dexp (succ n) = <bound+ 1 (exp2 n + exp2 n) (exp2 n + exp2 n) (dexp n)

-- Asymptotic growth of 2²ⁿ versus 2ⁿ. This will be needed in order to
-- prove the existence of a square root between any two dyadic
-- numbers.
asymp : ∀ a k
  → iszero k ≡ false
  → Σ ℕ (λ n → succ ((exp2 n * a) + (exp2 n * a)) < exp2 (n + n) * k ≡ true)
asymp a k p = 2 * (succ a) , lemma (succ (a + succ (a + zero))) refl (lemma0 (a + succ (a + 0)) k lemma0' p)
  where
    lemma0' : iszero (a + succ (a + 0)) ≡ false
    lemma0' rewrite +rsucc a (a + 0) = refl
    
    lemma0 : ∀ m k →
      iszero m ≡ false →
      iszero k ≡ false → succ m < (exp2 m + exp2 m) * k ≡ true
    lemma0 zero zero q ()
    lemma0 zero (succ k) q p rewrite +rsucc k (k + zero) = refl
    lemma0 (succ m) k q p rewrite
      *comm (exp2 m + exp2 m + (exp2 m + exp2 m)) k
      | *distr k (exp2 m + exp2 m) (exp2 m + exp2 m)
      | *comm k (exp2 m + exp2 m)
      = <+< 1 ((exp2 m + exp2 m) * k) (succ m) ((exp2 m + exp2 m) * k)
        (<bound* 1 (exp2 m + exp2 m) k (iszero< k p) (dexp m))
        (<bound* (succ m) (exp2 m + exp2 m) k (iszero< k p) (s1 m))
        where
          s1 : ∀ m → succ m < exp2 m + exp2 m ≡ true
          s1 zero = refl
          s1 (succ m) = <+< 1 (exp2 m + exp2 m) (succ m) (exp2 m + exp2 m) (dexp m) (s1 m)
          
    lemma : ∀ n
      → iszero n ≡ false
      → 2 * (succ a) < exp2 n * k ≡ true
      → succ (exp2 n * a + exp2 n * a) < exp2 (n + n) * k ≡ true
    lemma n α p rewrite
      +rzero a
      | exp2plus n n
      | inv (*distr (exp2 n) a a)
      = <trans (succ (exp2 n * (a + a))) (exp2 n * succ (succ a + a))
          (exp2 n * exp2 n * k)
          sub
          sub'         
       where
         sub' : exp2 n * succ (succ (a + a)) < exp2 n * exp2 n * k ≡ true
         sub' rewrite
           inv (*assoc (exp2 n) (exp2 n) k)
           | <mult-inj (succ (succ (a + a))) (exp2 n * k) (exp2 n) (exp2-notzero n)
           | +rsucc a a
           = p

         sub : succ (exp2 n * (a + a)) < exp2 n * succ (succ (a + a)) ≡ true
         sub rewrite
           *distr (exp2 n) 1 (succ (a + a))
           = <+< 1 (exp2 n * 1) (exp2 n * (a + a)) (exp2 n * succ (a + a))
             (s1 n α)
             s2
           where
             s1' : ∀ n
               → iszero n ≡ false
               → 1 < exp2 n ≡ true
             s1' zero ()
             s1' (succ n) β rewrite *runit (exp2 n + exp2 n) = dexp n
           
             s1 : ∀ n
               → iszero n ≡ false
               → 1 < exp2 n * 1 ≡ true
             s1 n rewrite *runit (exp2 n) = s1' n
             
             s2 : exp2 n * (a + a) < exp2 n * succ (a + a) ≡ true
             s2 rewrite
               <mult-inj (a + a) (succ (a + a)) (exp2 n) (exp2-notzero n)
               = <succ (a + a)

-- Existence of a squared dyadic rational between any two natural
-- numbers. This is a lemma used in the proof of the existence of a
-- square root between any two natural numbers.
diffsq : ∀ x y
  → x < y ≡ true
  → Σ ℕ (λ n → Σ ℕ (λ c → (exp2 (2 * n) * x < c ² ≡ true) × (exp2 (2 * n) * y < c ² ≡ false)))
diffsq x y p with <evd x y p
diffsq x y p | k , (q , α) with asymp (succ y) k (<iszero k α)
... | n , w with sqrbetween (exp2 (2 * n) * x) (exp2 (2 * n) * y) (exp2 n * (succ y)) (exp2 (2 * n) * k)
  s1 s2 s3
  where
    s1 : exp2 (n + (n + zero)) * x + exp2 (n + (n + zero)) * k ≡ exp2 (n + (n + zero)) * y
    s1 rewrite inv (*distr (exp2 (n + (n + zero))) x k) | q
      = refl
    s2 : succ (exp2 n * (succ y) + exp2 n * (succ y)) < exp2 (n + (n + zero)) * k ≡ true
    s2 rewrite
      +rzero n
      = w
    s3 : exp2 (n + (n + zero)) * y < ((exp2 n * succ y) ²) ≡ true
    s3 rewrite
      *comm (succ y) (exp2 n)
      | inv (*assoc (exp2 n) (succ y) (exp2 n * succ y))
      | +rzero n
      | exp2plus n n
      | *assoc (succ y) (exp2 n) (succ y)
      | *comm (succ y) (exp2 n)
      | inv (*assoc (exp2 n) (exp2 n) y)
      | <mult-inj (exp2 n * y) (exp2 n * succ y * succ y) (exp2 n) (exp2-notzero n)
      | inv (*assoc (exp2 n) (succ y) (succ y))
      | <mult-inj (y) (succ y * succ y) (exp2 n) (exp2-notzero n)
      | <bound+ y (succ y) (y * succ y) (<succ y)
      = refl
... | v = n , v
