\begin{code}
module Snippets where

  open import Base
  open import Equality
  open import EquationalReasoning
  open import numbers.Integers
  open import equivalence.Equivalence
  open import equivalence.EquivalenceComposition
  open import equivalence.Quasiinverses
  open import logic.Quotients
  open import algebra.Groups
  open import algebra.IntegerAction
  open import topology.Circle
  open import topology.FundamentalGroup
  open import equality.Univalence renaming (ua to UnivalenceAxiom)
  open import equality.FunctionExtensionality
  open import topology.FundGroupCircle
    hiding (loops; code; equiv-family; fundamental-group-of-the-circle; preserves-composition)
\end{code}
%<*circle>
\begin{code}
  -- Winds a loop n times on the circle.
  loops : ℤ → Ω S¹ base
  loops n = z-act (Ω-st S¹ base) n loop

  -- Uses univalence to unwind a path over the integers.
  code : S¹ → Type0
  code = S¹-ind Type0 ℤ (UnivalenceAxiom zequiv-succ)

  -- Creates an equivalence between paths and encodings.
  equiv-family : (x : S¹) → (base == x) ≃ code x
  equiv-family x = qinv-≃ (encode x) (decode x , (encode-decode x , decode-encode x))

  -- The fundamental group of the circle is the integers.  In this
  -- proof, univalence is crucial. The next lemma will prove that the
  -- equivalence in fact preserves the group structure.
  fundamental-group-of-the-circle : Ω S¹ base ≃ ℤ
  fundamental-group-of-the-circle = equiv-family base

  preserves-composition : ∀ n m → loops (n +ᶻ m) == loops n · loops m
  preserves-composition n m = z-act+ (Ω-st S¹ base) n m loop
\end{code}
%</circle>
