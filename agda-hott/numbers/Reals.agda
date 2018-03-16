-- open import Agda.Primitive

-- data ℕ : Set₀ where
--   zero : ℕ
--   succ : ℕ → ℕ
-- {-# BUILTIN NATURAL ℕ #-}

-- record foo : Set₁ where
--   field
--     P : Set₀

-- record bar : Set₂ where 
--   field
--     f : ℕ → foo
--     n : ℕ
--     a : f n

open import Base
open import logic.Propositions
open import numbers.Integers
open import numbers.Naturals
open import numbers.Rationals

module numbers.Reals where

  record ℝ : Type2 where
    field
      lower : ℚ → Type0
      upper : ℚ → Type0
      
      -- lowerprop : (q : ℚ) → isProp (lower q)
      -- upperprop : (q : ℚ) → isProp (upper q)
      
      lower_habit : Σ ℚ lower
      upper_habit : Σ ℚ upper

      -- lower_rounded : (q : ℚ) → Σ ℚ (λ r → (q < r) × lower r)
