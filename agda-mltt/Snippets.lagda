\begin{code}
{-# OPTIONS --type-in-type #-}
\end{code}

%<*nat>
\begin{code}
data nats : Set where
  zero  : nats
  suc   : (n : nats) → nats
\end{code}
%</nat>

\begin{code}
module Product where
  postulate
    A : Set
    B : A → Set
    b : {a : A} → B a
\end{code}
%<*mlttproduct>
\begin{code}
  f : (a : A) → B a
  f = λ a → b
\end{code}
%</mlttproduct>

%<*mlttsum>
\begin{code}
  record Σ (S : Set) (T : S → Set) : Set
    where
    constructor _,_
    field
      fst : S
      snd : T fst
\end{code}
%</mlttsum>

%<*mlttnat>
\begin{code}
  data ℕ : Set where
    zero  : ℕ
    succ   : (n : ℕ) → ℕ
    
  _+_ : ℕ → (ℕ → ℕ)
  zero   + m = m
  succ n + m = succ (n + m)
\end{code}
%</mlttnat>
\begin{code}
module Equalities where
\end{code}

%<*mltteq>
\begin{code}
  data _≡_ {A : Set} : A → A → Set where
    refl : {a : A} → a ≡ a
\end{code}
%</mltteq>

\begin{code}
module Eqrzero where
  open import Equality hiding (ap)
  open import Naturals hiding (ap ; +rzero) 
\end{code}

%<*mlttzero>
\begin{code}
  ap : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
  ap f refl = refl
  
  +rzero : (n : ℕ) → n + 0 ≡ n
  +rzero 0 = refl
  +rzero (succ n) = ap succ (+rzero n)
\end{code}
%</mlttzero>

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


\begin{code}
module Diaconescu where
  open import Base
  open import Prop
  open import Booleans
  open import Naturals
\end{code}

%<*wellpointed>
\begin{code}
  postulate
    wellPointed : {A B : Set} → {f g : A → B}
      → ((x : A) → f x ≡ g x)
      → f ≡ g
\end{code}
%</wellpointed>


%<*diaconescu>
\begin{code}
  postulate
    AxiomOfChoice : {A : Set} {B : Set} {R : A → B → Set}
      → ((a : A) → (∃ b ∈ B , (R a b)))
      ------------------------------------------
      → (∃ f ∈ (A → B), ((a : A) → R a (f a)))      

  LawOfExcludedMiddle : {P : Set} → P ∨ ¬ P
  LawOfExcludedMiddle {P} = Ex-elim
    (AxiomOfChoice λ { (Q , q) → Ex-elim q Ex-isProp λ { (u , v) → u ,, v  }})
    ∨-isProp λ { (f , α) → byCases f α }
    where
      A : Set
      A = Σ (Bool → Set) (λ Q → Ex Bool (λ b → Q b))
  
      R : A → Bool → Set
      R (P , _) b = P b
  
      U : Bool → Set
      U b = (b ≡ true) ∨ P
      V : Bool → Set
      V b = (b ≡ false) ∨ P
      Ua : A
      Ua = U , (true ,, rinl refl)
      Va : A
      Va = V , (false ,, rinl refl)
  
      module lemma (f : A → Bool) where
        eqf : (p : P) → f Ua ≡ f Va 
        eqf p = ap f (Σ-eq Ua Va (
          wellPointed λ
            { false → propext ∨-isProp ∨-isProp (λ _ → rinr p) (λ _ → rinr p)
            ; true  → propext ∨-isProp ∨-isProp (λ _ → rinr p) (λ _ → rinr p)
            }) (Ex-isProp _ _))
          
        refute : true ≡ false → P ∨ ¬ P
        refute ()
        byCases : (α : (x : A) → R x (f x)) → P ∨ ¬ P
        byCases α with f Ua ?? | f Va ??
        byCases α | inl x | inr y = rinr λ p → true≢false (inv x · (eqf p · y))
        byCases α | inl x | inl y = ∨-elim (α Va) ∨-isProp
          λ { (inl q) → refute (inv y · q) ; (inr p) → rinl p }
        byCases α | inr x | inl y = ∨-elim (α Ua) ∨-isProp
          λ { (inl q) → refute (inv q · x) ; (inr p) → rinl p }
        byCases α | inr x | inr y = ∨-elim (α Ua) ∨-isProp
          λ { (inl q) → refute (inv q · x) ; (inr p) → rinl p }
      open lemma public
  \end{code}
%</diaconescu>

\begin{code}
module isProp where
  open import Base
  open import Equality

  data ∥_∥ (A : Set) : Set where
    ∣_∣ : A → ∥ A ∥
\end{code}
%<*isprop>
\begin{code}
  isProp : Set → Set
  isProp A = ((x y : A) → x ≡ y)
  postulate trunc : {A : Set} → isProp ∥ A ∥
\end{code}
%</isprop>


%<*truncrec>
\begin{code}
  trunc-rec : {A : Set} {P : Set} → isProp P
    → (A → P)
    → ∥ A ∥ → P
  trunc-rec _ f ∣ x ∣ = f x
\end{code}
%</truncrec>

