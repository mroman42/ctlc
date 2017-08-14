\begin{code}
-- This proof is based on Thorsten Altenkirch notes on
-- Computer Aided Formal Reasoning (G53CFR, G54CFR),
-- Nottingham University.

{-#  OPTIONS --type-in-type #-}

module Russell where

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- Encoding of set-theoretical sets. This is a definition of
-- a Set indexed by an index type I. This definition crucially
-- uses Set : Set, as it is a Set taking a Set as an argument.
-- As Set is a reserved word, we use Aro = Set in esperanto.
data Aro : Set where
  aro : (Index : Set) → (Index → Aro) → Aro

-- Definition of membership.
-- An element is a member of the set if there exists an
-- index pointing to it on the set.
_∈_ : Aro → Aro → Set
x ∈ (aro Index a) = Σ Index (λ i → x ≡ a i)

_∉_ : Aro → Aro → Set
a ∉ b = (a ∈ b) → ⊥

-- Paradoxical set R. It contains all the sets that do not
-- contain themselves. The index type is the type of the
-- set that do not contain themselves.
R : Aro
R = aro (Σ Aro (λ a → a ∉ a)) proj₁


-- Lemma 1. Every set in R does not contain itself.
lemma1 : {X : Aro} → X ∈ R → X ∉ X
lemma1 ((X , proofX∉X) , refl) = proofX∉X

-- Lemma 2. Every set which does not contain itself is in R.
lemma2 : {X : Aro} → X ∉ X → X ∈ R
lemma2 {X} proofX∉X = ((X , proofX∉X) , refl)

-- Lemma 3. R does not contain itself
lemma3 : R ∉ R
lemma3 proofR∈R = lemma1 proofR∈R proofR∈R


-- Russell's paradox. We have arrived to a contradiction.
russellsparadox : ⊥
russellsparadox = lemma3 (lemma2 lemma3)
\end{code}


\begin{code}
-- Examples of sets. Von Neumann ordinals 0, 1 and 2.
∅ : Aro
∅ = aro ⊥ ⊥-elim

[∅] : Aro
[∅] = aro ⊤ (λ _ → ∅)

[∅,[∅]] : Aro
[∅,[∅]] = aro Bool (λ x → if x then ∅ else [∅])
\end{code}
