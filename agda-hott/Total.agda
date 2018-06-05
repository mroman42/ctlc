{-# OPTIONS --without-K #-}

-- Agda-hott library.
-- Author: Mario Román

-- Total.  Index for the complete library. This is an example library
-- following the Homotopy Theory Book in Agda. Verified proofs and
-- definitions follow the informal ones in the book.

-- 1. Basic types and functions.
open import Base
open import base.Universes
open import base.Empty
open import base.Unit

-- 2. Equalities and functions.
open import Equality
open import Composition
open import Homotopies

-- 3. The notion of equivalence in homotopy type theory.
open import equivalence.Equivalence
open import equivalence.EquivalenceComposition
open import equivalence.EquivalenceProp
open import equivalence.Halfadjoints
open import equivalence.Quasiinverses

-- 4. Extensions to the notion of equality. Univalence Axiom.
open import equality.DecidableEquality
open import equality.Sigma
open import equality.CartesianProduct
open import equality.FunctionExtensionality
open import equality.Univalence

-- 5. Levels of Logic and H-types.
open import logic.Contractible
open import logic.Propositions
open import logic.Sets
open import logic.Hedberg
open import logic.HLevels
open import logic.Truncation
open import logic.SetTruncation
open import logic.Relation
open import logic.Quotients
open import logic.QuotientsLemmas

-- 6. Numeric types.
open import numbers.Naturals
open import numbers.Integers

-- 7. Algebraic structures.
open import algebra.Monoids
open import algebra.Groups
open import algebra.IntegerAction

-- 8. Synthetic topology.
open import topology.Interval
open import topology.Circle
open import topology.FundamentalGroup
open import topology.FundGroupCircle





