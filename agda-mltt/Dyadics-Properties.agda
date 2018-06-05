{-# OPTIONS --without-K #-}

-- Agda-MLTT library.
-- Author: Mario Román.

-- Dyadics-Properties.  Some technical lemmas about dyadic numbers in
-- general that are used when constructing Dedekind reals.


module Dyadics-Properties where

open import Base
open import Booleans
open import Equality
open import Prop
open import Naturals using (ℕ)

-- We rename Dyadics in order to ease the reading and write shorter
-- proofs.
open import Dyadics public using (half) renaming
  ( D to F
  ; zer to zero
  ; oned to one
  ; _+d_ to _+_
  ; _*d_ to _*_
  ; _<d_ to _<_
  ; add-comm to +comm
  ; add-zero to +zero
  ; addhalfhalf to +half
  ; mult-comm to *comm
  ; mult-zero to *zero
  ; mult-one to *one
  ; lthalf to <half
  ; ltzero to <zero
  ; ltzeroref to <zeroref
  ; ltone to <one
  ; twod to two
  ; dec≡ to dec-eq
  ; add-assoc to +assoc
  ; mult-assoc to *assoc
  ; mustbezero to mustbezero
  ; mp-distr to *distr
  )
open import Dyadics-Ordering public using () renaming
  ( ltplus to <plus'
  ; ltmult to <mult
  ; dpositivity to <positivity
  ; ltevd to <evd
  ; leevd to <eevd
  ; +nonzero to +nonzero
  ; alwayspos to <apos
  ; <sqbt0 to <sqbt0
  ; <sqbetween-almost to <sqbetween-almost
  )


-- Cancellation and ordering.
<plus : (a b c : F) → (a + c) < (b + c) ≡ a < b
<plus a b c rewrite +comm a c | +comm b c = <plus' c a b


-- Order is transitive.
<trans : (a b c : F) → a < b ≡ true → b < c ≡ true → a < c ≡ true
<trans a b c p q with (<evd a b p) | (<evd b c q)
<trans a b c p q | d , (refl , β) | e , (refl , β2) rewrite
  (inv (+assoc a d e))
  | inv (+zero a)
  | inv (+assoc zero a (d + e))
  | +zero (a + (d + e))
  | +comm a (d + e)
  | <plus zero (d + e) a
  = +nonzero d e β

<plussmt : (a c : F) → a + c < c ≡ false
<plussmt a c rewrite
  inv (+zero c)
  | +assoc a zero c
  | <plus (a + zero) zero c
  | +comm a zero
  | +zero a
  = <apos a

<smtplus : (a b : F) → zero < b ≡ true → a < a + b ≡ true
<smtplus a b p rewrite
  inv (+zero a)
  | +comm zero a
  | inv (+assoc a zero b)
  | +comm a zero
  | +comm a (zero + b)
  | <plus zero (zero + b) a
  | +zero b
  | p
  = refl

<ltrans : (a b c : F)
  → a < b ≡ false
  → c < b ≡ true
  ------------------
  → c < a ≡ true
<ltrans a b c p q with <evd c b q | <eevd a b p
<ltrans a b c p q | k , (α , β) | h , γ rewrite
  inv γ
  | inv α
  | inv (+assoc c k h)
  = <smtplus c (k + h) (<positivity k h β)

cantbezero : (a b : F) → a < b ≡ true → zero < b ≡ true
cantbezero a b p with <evd a b p
... | c , (α , β) rewrite inv α = <ltrans (a + c) c zero (<plussmt a c) β

<etrans : (a b c : F)
  → a < b ≡ true
  → a < c ≡ false
  → c < b ≡ true
<etrans a b c p q with <eevd a c q | <evd a b p
... | (d , α) | (k , (β , γ)) rewrite
  inv β
  | inv α
  | inv (+zero c)
  | +comm zero c
  | inv (+assoc c zero d)
  | +zero d
  | +comm c zero = lemma
  where
    lemma : zero + c < c + d + k ≡ true
    lemma rewrite
      inv (+assoc c d k)
      | +comm c (d + k)
      | <plus zero (d + k) c
      = lemma2
      where
        lemma' : d < d + k ≡ F.dyadic 0 0 refl < k
        lemma' rewrite
          +comm d k
          | inv (+zero d)
          | +assoc k zero d
          | <plus zero (k + zero) d
          | +comm k zero
          | +zero k
          = refl
        lemma2 : zero < d + k ≡ true
        lemma2 rewrite cantbezero d (d + k) (lemma' · γ) = refl

-- Minimum of two rationals.
min : F → F → F
min a b with (a < b)
min a b | true = a
min a b | false = b

min-bound : (a b c : F)
  → a < b ≡ true
  → a < c ≡ true
  --------------
  → a < min b c ≡ true
min-bound a b c p q with (b < c)??
min-bound a b c p q | inl x rewrite x = p
min-bound a b c p q | inr x rewrite x = q

min-def1 : (a b c : F)
  → a < c ≡ true
  → min a b < c ≡ true
min-def1 a b c p with (a < b)??
min-def1 a b c p | inl x rewrite x = p
min-def1 a b c p | inr x rewrite x = <etrans a c b p x

min-def2 : (a b c : F)
  → b < c ≡ true
  → min a b < c ≡ true
min-def2 a b c p with (a < b)??
min-def2 a b c p | inl x rewrite x = <trans a b c x p
min-def2 a b c p | inr x rewrite x = p

min-or : (P : F → Set) → (a b : F) → P a → P b → P (min a b)
min-or P a b pa pb with (a < b)??
min-or P a b pa pb | inl x rewrite x = pa
min-or P a b pa pb | inr x rewrite x = pb

<halfone : half < one ≡ true
<halfone rewrite
  inv (+zero half)
  | inv +half
  | <plus zero half half
  | <half
  = refl
 

<halfpos : ∀ f
  → zero < f ≡ true
  -------------------------
  → zero < half * f ≡ true
<halfpos f p rewrite
  (inv (*zero half))
  | *comm zero half
  | <mult half zero f <half
  | *comm half zero
  | *zero half
  | p
  = refl

<halfless : ∀ f
  → zero < f ≡ true
  -----------------------
  → half * f < f ≡ true
<halfless f p rewrite
  inv (<mult half zero f <half)
  | *comm half zero
  | *zero half
  | inv (<plus zero (half * f) (half * f))
  | *comm half f
  | inv (*distr f half half)
  | +half
  | *comm f one
  | *one f
  | +zero (f * half)
  | p
  = refl

<plusone : ∀ f → f < one + f ≡ true
<plusone f rewrite
  inv (+zero f)
  | +assoc one zero f
  | <plus zero (one + zero) f
  | +comm one zero
  | +zero one
  | <one
  = refl

<pluscomp : ∀ a b c d
  → a < c ≡ true
  → b < d ≡ true
  → a + b < c + d ≡ true
<pluscomp a b c d p q = <trans (a + b) (c + b) (c + d) lemma1 lemma2
  where
    lemma1 : a + b < c + b ≡ true
    lemma1 rewrite <plus a c b | p = refl
    lemma2 : c + b < c + d ≡ true
    lemma2 rewrite +comm c b | +comm c d | <plus b d c | q = refl

<plus+zero : ∀ a b → a < a + b ≡ zero < b
<plus+zero a b rewrite
  inv (+zero a)
  | inv (+assoc zero a b)
  | +comm a b
  | +assoc zero b a
  | <plus zero (zero + b) a
  | +zero b
  = refl

halfsplit : (a : F) → a ≡ half * a + half * a
halfsplit a = inv (*one a) · lemma
  where
    lemma : one * a ≡ half * a + half * a
    lemma rewrite
      inv +half
      | *comm (half + half) a
      | *distr a half half
      | *comm half a
      = refl

-- Arithmetic mean of two numbers.
mean : F → F → F
mean a b = half * (a + b)

-- Mean inequalities.
<mean-max : (a b : F) → a < b ≡ a < mean a b
<mean-max a b = lemma · ap (λ u → u < mean a b) (inv (halfsplit a))
  where
    lemma : a < b ≡ half * a + half * a < mean a b
    lemma rewrite
      *distr half a b
      | +comm (half * a) (half * b)
      | <plus (half * a) (half * b) (half * a)
      | <mult half a b <half
      = refl

<mean-max' : (a b : F) → a < b ≡ true → a < mean a b ≡ true
<mean-max' a b p rewrite <mean-max a b | p = refl

<mean-min : (a b : F) → a < b ≡ mean a b < b
<mean-min a b = lemma · ap (λ u → mean a b < u) (inv (halfsplit b))
  where
    lemma : a < b ≡ mean a b < half * b + half * b
    lemma rewrite
      *distr half a b
      | <plus (half * a) (half * b) (half * b)
      | <mult half a b <half
      = refl

<mean-min' : (a b : F) → a < b ≡ true → mean a b < b ≡ true
<mean-min' a b p rewrite <mean-min a b | p = refl

<mean-max-true : (a b : F) → a < b ≡ true → a < mean a b ≡ true
<mean-max-true a b p rewrite inv p | inv (<mean-max a b) = refl

<mean-min-true : (a b : F) → a < b ≡ true → mean a b < b ≡ true
<mean-min-true a b p rewrite inv p | inv (<mean-min a b) = refl


-- Square root between rational numbers.
<sqless : ∀ a b
  → a * a < b * b ≡ true
  -----------------------
  → a     < b     ≡ true
<sqless a b p with (a < b)??
<sqless a b p | inl x = x
<sqless a b p | inr x with (a * b < b * b)??
<sqless a b p | inr x | inr y with (zero < a)??
... | inl z rewrite inv (<mult a a b z) = lemma
  where
    lemma : a * a < a * b ≡ true
    lemma = <ltrans (a * b) (b * b) (a * a) y p
... | inr z rewrite mustbezero a z | mustbezero b x | p = refl
<sqless a b p | inr x | inl y with (zero < b)??
... | inl z rewrite *comm a b | <mult b a b z = y
... | inr z rewrite mustbezero b z = exfalso (<zeroref (a * a) p)

<*zero : (b : F) → b * zero < b ≡ true → zero < b ≡ true
<*zero b q rewrite *comm b zero | (*zero b) = q

<sqcrec : ∀ a b
  → a < b ≡ true
  → a * a < b * b ≡ true
<sqcrec a b p with (zero < a)??
<sqcrec a b p | inl x with (zero < b)??
<sqcrec a b p | inl x | inl y = <trans (a * a) (b * a) (b * b) lemma2 lemma1
  where
    lemma1 : b * a < b * b ≡ true
    lemma1 rewrite <mult b a b y = p
    lemma2 : a * a < b * a ≡ true
    lemma2 rewrite *comm b a | <mult a a b x = p
<sqcrec a b p | inl x | inr y rewrite mustbezero b y = exfalso (<zeroref a p)
<sqcrec a b p | inr x rewrite
  <zero a x
  | *zero zero
  | inv (*zero b)
  | *comm zero b
  | <mult b zero b (<*zero b p)
  | *comm b zero
  | *zero b
  | p
  = refl


-- Technical lemmas on the dyadic rationals.
F-lemma1 : (x y d f r : F)
  → r + d ≡ f
  → x + y ≡ r
  ------------------------------------
  → x + half * d + (y + half * d) ≡ f
F-lemma1 x y d f r p q rewrite
  +assoc (x + (half * d)) y (half * d)
  | inv (+assoc x (half * d) y)
  | +comm (half * d) y
  | +assoc x y (half * d)
  | q
  | inv (+assoc r (half * d) (half * d))
  | *comm half d
  | inv (*distr d half half)
  | +half
  | *comm d one
  | *one d
  | p
  = refl

F-lemma2 : (x y : F) → zero < y ≡ true → x < x + y ≡ true
F-lemma2 x y p rewrite
  inv (+zero x)
  | +comm zero x
  | inv (+assoc x zero y)
  | <plus x zero y
  | +comm x zero
  | +comm x (zero + y)
  | +zero y
  | <plus zero y x
  | p
  = refl

F-lemma3 : (g : F) → g < (one + g) * (one + g) ≡ true
F-lemma3 g rewrite
  *distr (one + g) one g
  | *comm (one + g) one
  | *one (one + g)
  | +comm one g
  | inv (+assoc g one ((g + one) * g))
  | <plus+zero g (one + (g + one) * g)
  | <positivity one ((g + one) * g) <one
  = refl

F-lemma4 : (u f r : F)
  → u < r * r ≡ true
  → r < f     ≡ true
  → u < f * f ≡ true
F-lemma4 u f r p q = <trans u (r * r) (f * f) p (<sqcrec r f q)


F-lemma6 : (a g g' : F)
  → a < g * g ≡ true
  → a < g' * g' ≡ true
  → a < g * g' ≡ true
F-lemma6 a g g' p q with (g < g')??
F-lemma6 a g g' p q | inl x with (zero < g)??
F-lemma6 a g g' p q | inl x | inl x₁ = <trans a (g * g) (g * g') p (<mult g g g' x₁ · x)
F-lemma6 a g g' p q | inl x | inr x₁ rewrite mustbezero g x₁ = exfalso (<zeroref a p)
F-lemma6 a g g' p q | inr x with (zero < g')??
F-lemma6 a g g' p q | inr x | inl x₁ rewrite inv (<mult g' g g' x₁) | *comm g g'
  = <ltrans (g' * g) (g' * g') a x q
F-lemma6 a g g' p q | inr x | inr x₁ rewrite mustbezero g' x₁ | *comm g zero | *zero g = q


<sqbetween : (a b : F)
  → a < b ≡ true
  → Σ F (λ c → (a < c * c ≡ true) × (c * c < b ≡ true))
<sqbetween a b p with <sqbetween-almost a (mean a b) (inv (<mean-max a b) · p)
... | c , (α , β) = c , (α , (<etrans (mean a b) b (c * c) (<mean-min' a b p) β))
