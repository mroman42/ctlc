\begin{code}
{-# OPTIONS --type-in-type #-}
\end{code}

%<*nat>
\begin{code}
data ℕ : Set where
  zero  : ℕ
  suc   : (n : ℕ) → ℕ
\end{code}
%</nat>

\begin{code}
module SnippetReals where

  open import Base
  open import Booleans
  open import Equality
  open import Prop
  open import Naturals using (ℕ)
  open import Dyadics-Properties
\end{code}
%<*reals>
\begin{code}
  record ℝ⁺ : Set where
    constructor real
    field
     cut : F → Set
     isprop : (q : F) → isProp (cut q)
 
     bound : ∃ q ∈ F , cut q
     round1 : (q : F) → cut q → ∃ p ∈ F , ((p < q ≡ true) × cut p)
     round2 : (q : F) → (∃ p ∈ F , ((p < q ≡ true) × cut p)) → cut q
  open ℝ⁺ {{...}} public
\end{code}
%</reals>

\begin{code}
module Sqrt where
  open import Reals hiding (sqrt)
  open import Base
  open import Booleans
  open import Equality
  open import Prop
  open import Naturals using (ℕ)
  open import Dyadics-Properties

\end{code}

%<*sqrt>
\begin{code}
  sqrt : ℝ⁺ → ℝ⁺
  sqrt a = record
    { cut = λ f → ∃ g ∈ F , (cut {{a}} g × (g < f * f ≡ true))
    ; isprop = λ f → Ex-isProp
    ; bound = Ex-elim (bound {{a}}) Ex-isProp λ { (g , α) → one + g ,, (g ,, (α , F-lemma3 g)) }
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
\end{code}
%</sqrt>
