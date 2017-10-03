\begin{code}
module Ctlc where
\end{code}

Primer ejemplo de agda

%<*example>
\begin{code}
  -- An identity function
  id : ∀{l} {A : Set l} → A → A
  id a = a

  -- A constant function
  const : ∀{l} {A B : Set l} → A → B → A
  const a b = a

  -- Composition of functions
  _∘_ : ∀{l} {A B C : Set l} → (B → C) → (A → B) → A → C
  (g ∘ f) x = g (f x)
\end{code}
%</example>



Descripción de los tipos básicos de la teoría.

%<*mltt>
\begin{code}
  -- An inductive datatype is determined by a (possibly empty) list of
  -- constructors.
  data ⊥ : Set where

  data _+_ (S : Set) (T : Set) : Set where
    inl : S → S + T
    inr : T → S + T

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  -- A record is determined by a (possibly empty) list of fields that
  -- have to be filled in order to define an instance of the type.
  record ⊤ : Set where
   constructor unit

  record _∗_ (S : Set) (T : Set) : Set where
   constructor _,_
   field
    fst : S
    snd : T

  record Σ (S : Set)(T : S → Set) : Set where
    constructor _,_
    field
      fst : S
      snd : T fst

  -- Propositional equality is another example of inductive type,
  -- namely, the smallest type containing reflexivity. We define it at
  -- all levels of the universe hierarchy.
  data _==_ {l} {X : Set l} : X → X → Set l where
      refl : (x : X) → x == x
\end{code}
%</mltt>

%<*mlttproof>
\begin{code}
  -- Some simple proofs about types in Agda using pattern matching.
  -- Commutativity of the product.
  comm-∗ : {A : Set}{B : Set} → A ∗ B → B ∗ A
  comm-∗ (a , b) = (b , a)

  -- Associativity of the coproduct.
  assocLR-+ : {A B C : Set} → (A + B) + C → A + (B + C)
  assocLR-+ (inl (inl a)) = inl a
  assocLR-+ (inl (inr b)) = inr (inl b)
  assocLR-+ (inr c)       = inr (inr c)

  -- Principle of explosion. Ex falso quodlibet.
  exfalso : {X : Set} → ⊥ → X
  exfalso ()

  -- Projections of the dependent pair type.
\end{code}
%</mlttproof>

%<*theoremchoice>
\begin{code}
  ac : {A B : Set} → {R : A → B → Set} →
       ((x : A) → Σ B (λ y → R x y)) → (Σ (A → B) (λ f → (x : A) → R x (f x)))
  ac g = ({!!} ∘ {!!}) , {!!}
\end{code}
%</theoremchoice>
