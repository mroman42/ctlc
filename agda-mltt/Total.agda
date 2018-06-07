{-# OPTIONS --without-K #-}

-- Agda-MLTT library.
-- Author: Mario Román.

-- Total.  Index for the complete Agda-MLTT library. This is an
-- example library following the presentation of Martin-Löf type
-- theory on the text.

-- 1. Basic types and definitions.
open import Base
open import Equality
open import Prop

-- 2. Numeric types.
open import Booleans
open import Naturals
open import Dyadics
open import Dyadics-Ordering
open import Dyadics-Properties

-- 3. Construction of positive Dedekind cuts.
open import Reals

-- 4. Axiom of Choice and Diaconescu's theorem.
open import Etcs
