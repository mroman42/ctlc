\begin{code}
module Ctlc where
\end{code}

First Agda examples

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



Basic types of MLTT

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

  record _×_ (S : Set) (T : Set) : Set where
   constructor _,_
   field
    fst : S
    snd : T

  record Σ (A : Set)(B : A → Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B fst

  -- Propositional equality is another example of inductive type,
  -- namely, the smallest type containing reflexivity. We define it at
  -- all levels of the universe hierarchy.
  data _==_ {l} {A : Set l} (x : A) : A → Set l where
    refl : x == x
\end{code}
%</mltt>

%<*mlttproof>
\begin{code}
  -- Some simple proofs about types in Agda using pattern matching.
  -- Commutativity of the product.
  comm-∗ : {A : Set}{B : Set} → A × B → B × A
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
  -- Projections of the dependent pair type.
  proj1 : {A : Set} → {B : A → Set} → Σ A B → A
  proj1 (fst , snd) = fst

  proj2 : {A : Set} → {B : A → Set} → (p : Σ A B) → B (proj1 p)
  proj2 (fst , snd) = snd 

  -- Theorem of choice
  tc : {A B : Set} → {R : A → B → Set} →
       ((x : A) → Σ B (λ y → R x y)) → (Σ (A → B) (λ f → (x : A) → R x (f x)))
  tc {A} {B} {R} g = (λ x → proj1 (g x)) , (λ x → proj2 (g x))
\end{code}
%</theoremchoice>

%<*indiscernability>
\begin{code}
  -- Indiscernability of identicals proved by pattern matching. We
  -- only have to prove the case in which the equality is reflexivity.
  indiscernability : {A : Set} → {C : A → Set} →
    (x y : A) → (p : x == y) → C x → C y
  indiscernability _ _ refl = id
\end{code}
%</indiscernability>

%<*groupoids>
\begin{code}
  -- Inverse
  inv : {A : Set} → {x y : A} → x == y → y == x
  inv refl = refl

  -- Transitivity
  trans : {A : Set} → {x y z : A} → x == y → y == z → x == z
  trans refl refl = refl

  -- Neutrality of refl
  neutr-refl-L : {A : Set} → {x y : A} → (p : x == y) → p == trans p refl
  neutr-refl-R : {A : Set} → {x y : A} → (p : y == x) → p == trans refl p
  neutr-refl-L refl = refl
  neutr-refl-R refl = refl

  -- Concatenation of inverses
  inv-trans-L : {A : Set} → {x y : A} → (p : x == y) → trans (inv p) p == refl
  inv-trans-R : {A : Set} → {x y : A} → (p : x == y) → trans p (inv p) == refl
  inv-trans-L refl = refl
  inv-trans-R refl = refl

  -- The inverse is an involution
  inv-involution : {A : Set} → {x y : A} → (p : x == y) → inv (inv p) == p
  inv-involution refl = refl
\end{code}
%</groupoids>

%<*groupoid-functors>
\begin{code}
  -- Application of functions to paths
  ap : {A B : Set} → {x y : A} → (f : A → B) → x == y → f x == f y
  ap f refl = refl

  -- Functions act over equalities as applicative functors
  ap-funct-trans : {A B C : Set} → {x y z : A} →
    (f : A → B) → (g : A → B) → (p : x == y) → (q : y == z) →
    ap f (trans p q) == trans (ap f p) (ap f q)
  ap-funct-trans f g refl refl = refl

  ap-funct-inv : {A B : Set} → {x y : A} → (f : A → B) → (p : x == y) →
    ap f (inv p) == inv (ap f p)
  ap-funct-inv f refl = refl

  ap-funct-comp : {A B C : Set} → {x y : A} → (g : B → C) → (f : A → B) → (p : x == y) →
    ap g (ap f p) == ap (g ∘ f) p
  ap-funct-comp g f refl = refl

  ap-funct-id : {A B : Set} → {x y : A} → (p : x == y) → ap id p == p
  ap-funct-id refl = refl
\end{code}
%</groupoid-functors>


%<*eckmann-hilton>
\begin{code}
  -- Loop space
  Ω : ∀{l} (A : Set l) → (a : A) → Set l
  Ω A a = (a == a)

  -- Second loop space
  Ω² : ∀{l} (A : Set l) → (a : A) → Set l
  Ω² A a = (_==_) {_} {Ω A a} refl refl

  -- Horizontal composition
  _★_ : ∀{l} {A : Set l} → {a : A} → Ω² A a → Ω² A a → Ω² A a
  α ★ β = refl

  -- TODO: Why is it not necessary to use the proof of the book?
  eckmannhilton : {A : Set} → {a : A} → (α β : Ω² A a) → (trans α β) == (trans β α)
  eckmannhilton refl refl = refl
\end{code}
%</eckmann-hilton>
