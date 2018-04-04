{-# OPTIONS --type-in-type #-}

module Reals where

open import Base
open import Booleans
open import Equality
open import Prop

postulate
  F : Set
  zero : F
  one : F
  _+_ : F → F → F
  _*_ : F → F → F
  _<_ : F → F → Bool

infixl 30 _+_
infixl 35 _*_
infix 6 _<_

postulate
  -- Algebraic structure
  +comm : (a b : F) → a + b ≡ b + a
  +assoc : (a b c : F) → a + (b + c) ≡ a + b + c
  +zero : (a : F) → zero + a ≡ a

  *comm : (a b : F) → a * b ≡ b * a
  *assoc : (a b c : F) → a * (b * c) ≡ a * b * c
  *zero : (a : F) → zero * a ≡ zero
  *one : (a : F) → one * a ≡ a
  *distr : (a b c : F) → a * (b + c) ≡ a * b + a * c

  -- Ordered field
  <evd : (a b : F) → a < b ≡ true → Σ F (λ c → (a + c ≡ b) × (zero < c ≡ true))
  <trans : (a b c : F) → a < b ≡ true → b < c ≡ true → a < c ≡ true

  <zero : (a : F) → zero < a ≡ false → a ≡ zero
  <one : zero < one ≡ true
  <plus : (a b c : F) → (a + c) < (b + c) ≡ a < b
  <mult : (a b c : F) → zero < a ≡ true → a * b < a * c ≡ b < c

  <sqbetween : (a b : F) → a < b ≡ true → Σ F (λ c → (a < c * c ≡ true) × (c * c < b ≡ true))
  <positivity : (a b : F) → zero < a ≡ true → zero < a + b ≡ true

  -- Half
  half : F
  <half : zero < half ≡ true
  +half : half + half ≡ one

  -- Decidable equality
  dec-eq : (a b : F) → (a ≡ b) ⊎ ¬ (a ≡ b)

<trans' : (a b c : F) → a < b ≡ true → b < c ≡ true → a < c ≡ true
<trans' a b c p q with (<evd a b p) | (<evd b c q)
<trans' a b c p q | d , (refl , β) | e , (refl , β2) rewrite
  (inv (+assoc a d e))
  | inv (+zero a)
  | inv (+assoc zero a (d + e))
  | +zero (a + (d + e))
  | +comm a (d + e)
  | <plus zero (d + e) a
  = {!!}

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
min-def1 a b c p | inr x rewrite x = {!!}

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

mean : F → F → F
mean a b = half * (a + b)

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

<mean-min : (a b : F) → a < b ≡ mean a b < b
<mean-min a b = lemma · ap (λ u → mean a b < u) (inv (halfsplit b))
  where
    lemma : a < b ≡ mean a b < half * b + half * b
    lemma rewrite
      *distr half a b
      | <plus (half * a) (half * b) (half * b)
      | <mult half a b <half
      = refl

<mean-max-true : (a b : F) → a < b ≡ true → a < mean a b ≡ true
<mean-max-true a b p rewrite inv p | inv (<mean-max a b) = refl

<mean-min-true : (a b : F) → a < b ≡ true → mean a b < b ≡ true
<mean-min-true a b p rewrite inv p | inv (<mean-min a b) = refl

<sqless : ∀ a b
  → a * a < b * b ≡ true
  -----------------------
  → a     < b     ≡ true
<sqless a b p with (a < b)??
<sqless a b p | inl x = x
<sqless a b p | inr x with (a * b < b * b)??
<sqless a b p | inr x | inr y = {!!}
<sqless a b p | inr x | inl y = {!!}
-- Usando que (a < b) es decidible

<*zero : (b : F) → b * zero < b ≡ true → zero < b ≡ true
<*zero b q rewrite *comm b zero | (*zero b) = q

<sqcrec : ∀ a b
  → a < b ≡ true
  → a * a < b * b ≡ true
<sqcrec a b p with (zero < a)??
<sqcrec a b p | inl x with (zero < b)??
<sqcrec a b p | inl x | inl y = <trans (a * a) (b * a) (b * b) {!<mult a b a!} {!!}
<sqcrec a b p | inl x | inr y = {!!}
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

F-lemma5 : (y' z' y z f : F)
  → y' < y ≡ true
  → z' < z ≡ true
  → y * z ≡ f
  → y' * z' < f ≡ true
F-lemma5 y' z' y z .(y * z) α β refl with (zero < y')??
F-lemma5 y' z' y z .(y * z) α β refl | inl x = <trans (y' * z') (y' * z) (y * z) {!!} {!!}
F-lemma5 y' z' y z .(y * z) α β refl | inr x = {!!} -- <trans (y' * z') (y * z') (y * z) sublemma1 sublemma2
  where
    sublemma1 : y' * z' < y * z' ≡ true
    sublemma1 = {!!}

    sublemma2 : y * z' < y * z ≡ true
    sublemma2 = {!!}


F-lemma6 : (a g g' : F)
  → a < g * g ≡ true
  → a < g' * g' ≡ true
  → a < g * g' ≡ true
F-lemma6 = {!!}

F-lemma7 : (a b c : F)
  → a * b < c ≡ true
  → Σ F (λ s → (zero < s ≡ true) × ((a + s) * b ≡ c))
F-lemma7 a b c p = {!!}

F-lemma8 : (a b : F) → min a b * min a b < a * b ≡ true
F-lemma8 = {!!}

--------------------------------------------------------
--------------------------------------------------------
--- REALS ----------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
record ℝ⁺ : Set where
  constructor real
  field
    -- Dedekind cut
    cut : F → Set
    isprop : (f : F) → isProp (cut f)
    bound : ∃ f ∈ F , cut f
    round1 : (f : F) → cut f → ∃ r ∈ F , ((r < f ≡ true) × cut r)
    round2 : (f : F) → (∃ r ∈ F , ((r < f ≡ true) × cut r)) → cut f
open ℝ⁺ {{...}} public

real-eq' : (a b : ℝ⁺) → ((f : F) → cut {{a}} f ≡ cut {{b}} f) → a ≡ b
real-eq' (real cuta ispropa bounda round1a round2a) (real cutb ispropb boundb round1b round2b) α with funext α
real-eq' (real cuta ispropa bounda round1a round2a) (real .cuta ispropb boundb round1b round2b) α
  | refl with prop-eq | bound-eq | round1-eq | round2-eq
  where 
    prop-eq : ispropa ≡ ispropb
    prop-eq = (pi-isProp λ n x y → funext λ z → funext λ w → uip (x z w) (y z w)) ispropa ispropb
    bound-eq : bounda ≡ boundb
    bound-eq = Ex-isProp bounda boundb
    round1-eq : round1a ≡ round1b
    round1-eq = (pi-isProp λ a x y → funext λ z → Ex-isProp (x z) (y z)) round1a round1b
    round2-eq : round2a ≡ round2b
    round2-eq = (pi-isProp λ a x y → funext (λ x₁ → ispropb a (x x₁) (y x₁))) round2a round2b
real-eq' (real cuta ispropa bounda round1a round2a) (real .cuta .ispropa boundb round1b round2b) α
  | refl | refl | refl | refl | refl = refl

postulate prop-univ : {A B : Set} → isProp A → isProp B → (A → B) → (B → A) → A ≡ B

real-eq : (a b : ℝ⁺)
  → ((f : F) → (cut {{a}} f → cut {{b}} f))
  → ((f : F) → (cut {{b}} f → cut {{a}} f))
  → a ≡ b
real-eq a b α β = real-eq' a b lemma
  where
    lemma : (f : F) → (cut {{a}} f ≡ cut {{b}} f)
    lemma f = prop-univ (isprop {{a}} f) (isprop {{b}} f) (α f) (β f)

r0 : ℝ⁺
r0 = record
  { cut = λ x → zero < x ≡ true
  ; isprop = λ f → uip
  ; bound = one ,, <one
  ; round1 = λ f x → (half * f) ,, (<halfless f x , <halfpos f x)
  ; round2 = λ f x → Ex-elim x uip λ { (r , (α , β)) → <trans zero r f β α }
  }

rat : F → ℝ⁺
rat q = record
  { cut = λ x → q < x ≡ true 
  ; isprop = λ f → uip
  ; bound = (one + q) ,, <plusone q
  ; round1 = λ { f x → mean q f ,, (<mean-min-true q f x , <mean-max-true q f x) }
  ; round2 = λ f x → Ex-elim x uip λ { (r , (α , β)) → <trans q r f β α }
  }


infixl 30 _+ᵣ_
_+ᵣ_ : ℝ⁺ → ℝ⁺ → ℝ⁺
a +ᵣ b = record
  { cut = λ x → ∃ y ∈ F , (∃ z ∈ F , ((cut {{a}} y × cut {{b}} z) × (y + z ≡ x)))
  ; isprop = λ f → Ex-isProp
  ; bound =
     Ex-elim (bound {{a}}) Ex-isProp λ { (y , α) →
     Ex-elim (bound {{b}}) Ex-isProp λ { (z , β) →
     y + z ,, (y ,, (z ,, ((α , β) , refl)))
     }}
  ; round1 = λ f x →
      Ex-elim x Ex-isProp λ { (u , p) →
      Ex-elim p Ex-isProp λ { (v , ((p , q) , refl)) →
      Ex-elim (round1 {{a}} u p) Ex-isProp λ { (i , (ia , ib)) →
      Ex-elim (round1 {{b}} v q) Ex-isProp λ { (j , (ja , jb)) →
      (i + j) ,, (<pluscomp i j u v ia ja , (i ,, (j ,, ((ib , jb) , refl))))
      }}}}
  ; round2 = λ f x →
      Ex-elim x Ex-isProp λ { (r , (α , p)) →
      Ex-elim p Ex-isProp λ { (x , q) →
      Ex-elim q Ex-isProp λ { (y , ((u , v) , β)) →
      Σ-elim (<evd r f α) λ { (d , (γ1 , γ2)) →
      x + half * d ,, (y + half * d ,,
        ((round2 {{a}} (x + half * d) (x ,, (F-lemma2 x (half * d) (<halfpos d γ2) , u)) ,
          round2 {{b}} (y + half * d) (y ,, (F-lemma2 y (half * d) (<halfpos d γ2) , v))) ,
        F-lemma1 x y d f r γ1 β)
      ) 
      }}}}
  }
  

r+comm : (a b : ℝ⁺) → (a +ᵣ b) ≡ (b +ᵣ a)
r+comm a b = real-eq (a +ᵣ b) (b +ᵣ a) (lemma a b) (lemma b a)
  where
    lemma : ∀ a b → (f : F) → ℝ⁺.cut (a +ᵣ b) f → ℝ⁺.cut (b +ᵣ a) f
    lemma a b f α =
      Ex-elim α Ex-isProp λ { (x , h) →
      Ex-elim h Ex-isProp λ { (y , ((β , γ) , δ)) →
      y ,, (x ,, ((γ , β) , sublemma x y f δ))  
      }}
      where
        sublemma : (x y f : F) → x + y ≡ f → y + x ≡ f
        sublemma x y f p rewrite +comm x y | p = refl

sqrt : ℝ⁺ → ℝ⁺
sqrt a = record
  { cut = λ f → ∃ g ∈ F , (cut {{a}} g × (g < f * f ≡ true))
  ; isprop = λ f → Ex-isProp
  ; bound =
     Ex-elim (bound {{a}}) Ex-isProp λ { (g , α) →
     one + g ,, (g ,, (α , F-lemma3 g))
     }
  ; round1 = λ f x →
      Ex-elim x Ex-isProp λ { (g , (α , β)) →
      Σ-elim (<sqbetween g (f * f) β) λ { (r , (γ , δ)) →
      r ,, (<sqless r f δ , (g ,, (α , γ))) 
      }}
  ; round2 = λ f x →
      Ex-elim x Ex-isProp λ { (r , (α , h)) →
      Ex-elim h Ex-isProp λ { (u , (β , p)) →
      u ,, (β , F-lemma4 u f r p α) 
      }}
  }


_*ᵣ_ : ℝ⁺ → ℝ⁺ → ℝ⁺
a *ᵣ b = record
  { cut = λ x → ∃ y ∈ F , (∃ z ∈ F , ((cut {{a}} y × cut {{b}} z) × (y * z ≡ x)))
  ; isprop = λ f → Ex-isProp
  ; bound =
     Ex-elim (bound {{a}}) Ex-isProp λ { (x , α) → 
     Ex-elim (bound {{b}}) Ex-isProp λ { (y , β) →
     x * y ,, (x ,, (y ,, ((α , β) , refl)))     
     }}
  ; round1 = λ f x →
     Ex-elim x Ex-isProp λ { (y , u1) →
     Ex-elim u1 Ex-isProp λ { (z , ((αy , αz) , β )) →
     Ex-elim (round1 {{a}} y αy) Ex-isProp λ { (y' , (γ , αy')) →
     Ex-elim (round1 {{b}} z αz) Ex-isProp λ { (z' , (δ , αz')) →
     y' * z' ,, (F-lemma5 y' z' y z f γ δ β , (y' ,, (z' ,, ((αy' , αz') , refl)))) 
     }}}}
  ; round2 = λ f x →
     Ex-elim x Ex-isProp λ { (r , (α , x2)) →
     Ex-elim x2 Ex-isProp λ { (y , x3) →
     Ex-elim x3 Ex-isProp λ { (z , ((β1 , β2) , refl)) →
     Σ-elim (F-lemma7 y z f α) λ { (s , (ω , κ)) →
     y + s ,, (z ,, (((round2 {{a}} (y + s) (y ,, (((<plus+zero y s) · ω) , β1))) , β2) , κ))
     }}}}
  }


sqrt*linv : ∀ a → sqrt a *ᵣ sqrt a ≡ a
sqrt*linv a = real-eq (sqrt a *ᵣ sqrt a) a lemma lemma2
  where
    lemma : (f : F) → ℝ⁺.cut (sqrt a *ᵣ sqrt a) f → ℝ⁺.cut a f
    lemma f m =
      Ex-elim m (isprop {{a}} f) λ { (g , h) →
      Ex-elim h (isprop {{a}} f) λ { (g' , ((cg , cg') , refl)) →
      Ex-elim cg (isprop {{a}} f) λ { (j , (α , β)) →
      Ex-elim cg' (isprop {{a}} f) λ { (j' , (α' , β')) →
      round2 {{a}} f (min j' j ,,
        (F-lemma6 (min j' j) g g' (min-def2 j' j (g * g) β) ((min-def1 j' j (g' * g') β'))
        , min-or (cut {{a}}) j' j α' α)
        )
      }}}}

    lemma2 : (f : F) → ℝ⁺.cut a f → ℝ⁺.cut (sqrt a *ᵣ sqrt a) f
    lemma2 f m =
      Ex-elim (round1 {{a}} f m) Ex-isProp λ { (r , (h , n)) →
      Σ-elim (<sqbetween r f h) λ { (c , (α , β)) →
      round2 {{sqrt a *ᵣ sqrt a}} f (c * c ,,
      (β , (c ,, (c ,, (((r ,, (n , α)) , (r ,, (n , α))) , refl
      )))))}}

sqrt*rinv : ∀ a → sqrt (a *ᵣ a) ≡ a
sqrt*rinv a = real-eq (sqrt (a *ᵣ a)) a lemma lemma2
  where
    lemma : (f : F) → ℝ⁺.cut (sqrt (a *ᵣ a)) f → ℝ⁺.cut a f
    lemma f m =
      Ex-elim m (isprop {{a}} f) λ { (g , (α1 , β)) →
      Ex-elim α1 (isprop {{a}} f) λ { (y , α2) →
      Ex-elim α2 (isprop {{a}} f) λ { (z , ((γ1 , γ2) , refl)) →
      round2 {{a}} f (min y z ,,
        ( <sqless (min y z) f (<trans (min y z * min y z) (y * z) (f * f) (F-lemma8 y z) β)
        , min-or ((cut {{a}})) y z γ1 γ2)
        ) 
      }}}
      
    lemma2 : (f : F) → ℝ⁺.cut a f → ℝ⁺.cut (sqrt (a *ᵣ a)) f
    lemma2 f m =
      Ex-elim (round1 {{a}} f m) Ex-isProp λ { (r , (α , β)) →
      r * r ,,
      ( (r ,, (r ,, ((β , β) , refl)))
      , <sqcrec r f α
      )}



-----------------
-- LOCATORS
-----------------

Locator : (r : ℝ⁺) → Set
Locator r = (q : F) → (cut {{r}} q) ⊎ ¬ (cut {{r}} q)


loc-rational : (f : F) → Locator (rat f)
loc-rational f q with (f < q)??
loc-rational f q | inl x = inl x
loc-rational f q | inr x rewrite x = inr λ y → true≢false (inv y)
