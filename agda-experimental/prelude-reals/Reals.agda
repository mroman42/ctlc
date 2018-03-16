module Reals where

-- open import base.Base
open import Prop
open import Prelude
open import Structure.Smashed
-- open import Prelude.Smashed
-- open import SageRationals

open import Numeric.Rational renaming (Rational to ℚ)
open import Numeric.Nat.GCD
open import Numeric.Nat.Divide
open import Numeric.Nat.Prime
open import Numeric.Nat.Properties
open import Tactic.Nat


-- Hay forma de ahorrarse trabajar con el módulo Prop?
-- Y de paso ahorrarse type-in-type
-- Solo usando ∃ y ∨, y comprobando irrelevancia de lower y upper



-- TODO
--  1. Positive reals.
--  0! Rationals! whose predicates cannot depend on construction. (prelude?)
--  2. Decidable equalities on rationals
--  3. that rewrite to equalities on natural numbers
--  4. provable using prelude tactics.
--  5. IsProp-based propositions, without --type-in-type.
--  6. Definition of * is easy (???) in positive reals.
--  7. Check that the square root of 2 is in fact a square root.
--  8. Computable digits of the square root using rationals.

-- Auto tactic
test : (n m m' : Nat) → {{_ : NonZero n}} → n * m ≡ n * m' → m ≡ m'
test n m m' p = mul-inj₂ n m m' p

-- Less than postulate
--   _<ᵣ_ : ℚ → ℚ → Set

-- Formal fractions
-- data Fraction : Set where
--   frac : (a b : Nat) → {{_ : NonZero b}} → Fraction

-- _<ᶠ_ : Fraction → Fraction → Set
-- frac a₁ b₁ <ᶠ frac a₂ b₂ = a₁ * b₂ < a₂ * b₁

lem : ∀ {p q eq p₁ q₁ eq₁} {{_ : NonZero q}} {{_ : NonZero q₁}} →
          p ≡ p₁ → q ≡ q₁ → ratio p q eq ≡ ratio p₁ q₁ eq₁
lem {q = zero} {{}}
lem {q = suc q} refl refl = ratio _ _ $≡ smashed

-- TODO: Crear instancia Ord para los racionales
_<ᵣ_ : ℚ → ℚ → Set
p <ᵣ q = numerator p * denominator q < numerator q * denominator p


postulate
  ASSERT : {A : Set} → A

div-coprime : ∀ {a} {b} {c} → Coprime a c → a Divides (b * c) → a Divides b
div-coprime = ASSERT

rational-equality : ∀ {a} {b} → numerator a * denominator b ≡ numerator b * denominator a → a ≡ b
rational-equality {ratio p q {{r}} prf} {ratio p₁ q₁ {{r₁}} prf₁} α = lem (divides-antisym p|p₁ p₁|p) ASSERT
  where
    p|p₁q : p Divides (p₁ * q)
    p|p₁q rewrite (sym α) = divides-mul-l q₁ divides-refl

    p|p₁ : p Divides p₁
    p|p₁ = div-coprime prf p|p₁q

    p₁|p : p₁ Divides p
    p₁|p = ASSERT





data LessRat p q : Set where
  cross : numerator p * denominator q < numerator q * denominator p → LessRat p q

data LessEqRat p q : Set where
  cross : numerator p * denominator q ≤ numerator q * denominator p → LessEqRat p q

compareRat : ∀ p q → Comparison LessRat p q
compareRat p q with (compare {{OrdNat}} (numerator p * denominator q) (numerator q * denominator p))
compareRat p q | less lt = less (cross lt)
compareRat p q | equal eq = equal (rational-equality eq)
compareRat p q | greater gt = greater (cross gt)

instance
  OrdRat : Ord ℚ
  Ord._<_ OrdRat = LessRat
  Ord._≤_ OrdRat = LessEqRat
  Ord.compare OrdRat = compareRat


mkratio-<-sound : (a b : Nat) → {{_ : NonZero b}} → (p : ℚ) →
  (a * denominator p < numerator p * b) → (mkratio a b <ᵣ p)
mkratio-<-sound a b {{bnz}} p α with (gcd a b)
mkratio-<-sound .(q * 0) .(q₁ * 0) {{x}} p α
  | gcd-res zero (is-gcd (factor q refl) (factor q₁ refl) g) = refute α
mkratio-<-sound .(q * suc d) .(q₁ * suc d) {{x}} p α
  | gcd-res (suc d) (is-gcd (factor q refl) (factor q₁ refl) g) = {!mul-inj₁!}
  

-- mkratio< : (p₁ q₁ : Nat) → {{_ : NonZero q₁}} → (p₂ q₂ : Nat) → {{_ : NonZero q₂}} →
--   (p₁ * q₂ < p₂ * q₁) → (mkratio p₁ q₁ <ᵣ mkratio p₂ q₂)
-- mkratio< p₁ q₁ p₂ q₂ α with (gcd p₁ q₁) | (gcd p₂ q₂)
-- mkratio< p₁ q₁ p₂ q₂ α | gcd-res d (is-gcd (factor q eq) (factor q₃ eq₁) _) | gcd-res d₁ (is-gcd (factor q₄ eq₂) (factor q₅ eq₃) _) = {!by eq eq₁ eq₂ eq₃!}
--   where
--     lemma : (q q₁ q₂ q₃ q₄ q₅ d d₁ : Nat)
--       → ((q * d) * q₂ < (q₄ * d₁) * q₁)
--       → (q * q₅ < q₄ * q₃)
--     lemma = {!!}


-- Positive real numbers
record ℝ : Set₁ where
  field
    -- Dedekind cuts are
    lower : ℚ → Set
    upper : ℚ → Set
  
    -- Propositional
    lprop : (q : ℚ) → isProp (lower q)
    uprop : (q : ℚ) → isProp (upper q)

    -- Inhabited
    lhabit : ∃ ℚ lower
    uhabit : ∃ ℚ upper

    -- Rounded
    lround-1 : (q : ℚ) → lower q → ∃ ℚ (λ r → (q <ᵣ r) × lower r)
    lround-2 : (q : ℚ) → ∃ ℚ (λ r → (q <ᵣ r) × lower r) → lower q
    uround-1 : (q : ℚ) → upper q → ∃ ℚ (λ r → (r <ᵣ q) × upper r)
    uround-2 : (q : ℚ) → ∃ ℚ (λ r → (r <ᵣ q) × upper r) → upper q

    -- Disjoint
    disjoint : (q : ℚ) → ¬ (lower q × upper q)

    -- Located
    located : (q r : ℚ) → (q <ᵣ r) → (lower q ∨ upper r)
open ℝ public


-- real0 : ℝ
-- real0 = record
--   { lower = λ x → x <ᵣ (0 % 1) ≡ true
--   ; upper = λ x → (0 % 1) <ᵣ x ≡ true
--   ; lprop = λ q → uip
--   ; uprop = λ q → uip
--   ; lhabit = (-ᵣ (1 % 1))  ,, ASSUME
--   ; uhabit = (1 % 1) ,, ASSUME
--   ; lround-1 = λ q p → (q *ᵣ (1 % 2)) ,, (ASSUME , ASSUME)
--   ; lround-2 = λ q x → ∃-elim x uip (λ { (r , (α , β)) → ASSUME })
--   ; uround-1 = λ q x → (q *ᵣ (1 % 2)) ,, (ASSUME , ASSUME)
--   ; uround-2 = λ q x → ∃-elim x uip λ { (r , (α , β)) → ASSUME }
--   ; disjoint = λ q x → ASSUME  -- Absurds from Assume
--   ; located = λ q r x → ASSUME 
--   }
