{-# OPTIONS --type-in-type #-}

module Reals where

open import Base
open import Booleans
open import Equality
open import Prop
open import Naturals using (ℕ)
open import Dyadics-Properties


-- The following is a construction of the positive real numbers using
-- Dedekind cuts. A cut is a propositional predicate over the rational
-- numbers that determines which rationals are greater or equal than the
-- real number. A real number must be
--   * bounded, meaning that the cut must be inhabited;
--   * rounded, meaning that the cut must be an upper-unbounded and
--     nonclosed interval.
record ℝ⁺ : Set where
  constructor real
  field
    -- Dedekind cut
    cut : F → Set
    isprop : (q : F) → isProp (cut q)

    bound : ∃ q ∈ F , cut q
    round1 : (q : F) → cut q → ∃ p ∈ F , ((p < q ≡ true) × cut p)
    round2 : (q : F) → (∃ p ∈ F , ((p < q ≡ true) × cut p)) → cut q
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

real-eq : (a b : ℝ⁺)
  → ((f : F) → (cut {{a}} f → cut {{b}} f))
  → ((f : F) → (cut {{b}} f → cut {{a}} f))
  → a ≡ b
real-eq a b α β = real-eq' a b lemma
  where
    lemma : (f : F) → (cut {{a}} f ≡ cut {{b}} f)
    lemma f = propext (isprop {{a}} f) (isprop {{b}} f) (α f) (β f)


-- Examples of real numbers. Zero is a real number. Each rational
-- determines a real number.
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


-- Addition is an operation on real numbers. Addition is
-- commutative. This is an example on how theorems on the real numbers
-- could be proved.
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


-- Every positive real has a square root.
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


cutnonzero : (a : ℝ⁺) → (f : F) → ℝ⁺.cut a f → zero < f ≡ true
cutnonzero a f p = Ex-elim (round1 {{a}} f p) uip λ { (r , (β , _)) → cantbezero r f β }



-- A number is located if we can decide whether a rational number is
-- greater or equal than it. This can be used to compute decimal
-- digits of the number. In this example, we provide a locator for
-- sqrt(2) and we use it to compute some of its digits.
Locator : (r : ℝ⁺) → Set
Locator r = (q : F) → (cut {{r}} q) ⊎ ¬ (cut {{r}} q)

loc-rational : (f : F) → Locator (rat f)
loc-rational f q with (f < q)??
loc-rational f q | inl x = inl x
loc-rational f q | inr x rewrite x = inr λ y → true≢false (inv y)

locate : (r : ℝ⁺) → Locator r → (q : F) → Bool
locate r loc q with loc q
locate r loc q | inl x = true
locate r loc q | inr x = false

loc-sqrt2 : Locator (sqrt (rat (one + one)))
loc-sqrt2 q with (one + one < q * q)??
loc-sqrt2 q | inl x = inl (mean (one + one) (q * q) ,,
  (<mean-max' (one + one) (q * q) x , <mean-min' two (q * q) x)
  )
loc-sqrt2 q | inr x = inr λ α →
  Ex-elim α (λ _ → λ ()) λ { (f , (u , v)) →
  lemma (one + one) f (q * q) u v x
  }
  where
    lemma : ∀ a b c
      → a < b ≡ true
      → b < c ≡ true
      → a < c ≡ false
      -----------------
      → ⊥
    lemma a b c p q r rewrite (<trans a b c p q) = true≢false r

-- Example setup.
sqrt2 : ℝ⁺
sqrt2 = sqrt (rat (one + one))

data List (A : Set) : Set where
  []   : List A
  _∷_ : A → List A → List A  
infixr 45 _∷_

postulate
  Bit : Set
  O : Bit
  I : Bit

locateBit : (r : ℝ⁺) → Locator r → (q : F) → Bit
locateBit r loc q with loc q
locateBit r loc q | inl x = O
locateBit r loc q | inr x = I

digits : (r : ℝ⁺) → Locator r → (steps : ℕ) → (base ε : F) → List Bit
digits r loc ℕ.zero base ε = locateBit r loc (base + ε) ∷ []
digits r loc (ℕ.succ n) base ε with locate r loc (base + ε)
digits r loc (ℕ.succ n) base ε | true = O ∷ digits r loc n base (half * ε)
digits r loc (ℕ.succ n) base ε | false = I ∷ digits r loc n (base + ε) (half * ε)


-- Compilation through Haskell.
-- agda --compile Reals.agda --ghc-flag=-dynamic && ./Reals
open import Agda.Builtin.IO

postulate
  Unit : Set
  printBit : Bit → IO Unit
  printBitList : List Bit → IO Unit  

{-# COMPILE GHC List = data [] ([] | (:)) #-}
{-# COMPILE GHC Unit = type () #-}
{-# COMPILE GHC Bit = type Int #-}
{-# COMPILE GHC I = 1 #-}
{-# COMPILE GHC O = 0 #-}
{-# COMPILE GHC printBit = Prelude.print #-}
{-# COMPILE GHC printBitList = Prelude.print #-}

main : IO Unit
main = printBitList (digits sqrt2 loc-sqrt2 10 one half)
-- [0,1,1,0,1,0,1,0,0,0,0,0]
