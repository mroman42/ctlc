-- Renaming Agda primitive builtins.
open import Agda.Primitive public
Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ

data _≡_ {ℓ} {A : Type ℓ} : A → A → Type ℓ where
  refl : {a : A} → a ≡ a
infixl 4 _≡_ 
{-# BUILTIN EQUALITY _≡_ #-}

postulate
  funext : ∀ {ℓ}{A B : Type ℓ} → (f g : A → B) → ((a : A) → f a ≡ g a) → f ≡ g

-- On how to use monads in functional programming.
id : ∀ {ℓ} {A : Type ℓ} → A → A
id a = a

_∘_ : ∀ {ℓ} {A B C : Type ℓ} → (B → C) → (A → B) → (A → C)
(f ∘ g) x = f (g x)

record Endofunctor {ℓ} (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field
    -- A functor is determined by how it acts on arrows.
    map : ∀ {X Y} → (X → Y) → F X → F Y

    -- A functor must preserve identity and composition.
    map-id   : ∀ {X} →                              map (id {_} {X}) ≡ id
    map-comp : ∀ {X Y Z} {g : X → Y} {f : Y → Z} →  map (f ∘ g)      ≡ (map f) ∘ (map g)
open Endofunctor {{...}} public

record Monad {ℓ} (T : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field
    monad-functor : Endofunctor T
    η : ∀ {X} →    X       → T X
    μ : ∀ {X} →    T (T X) → T X
open Monad {{...}} public
  


-- Lists
data List {ℓ} (A : Type ℓ) : Type ℓ where
  [] : List A
  _∷_ : A → List A → List A

list-map : ∀ {ℓ} {A B : Type ℓ} → (A → B) → List A → List B
list-map f [] = []
list-map f (x ∷ l) = f x ∷ list-map f l

list-map-id : ∀ {ℓ} {A : Type ℓ} → (l : List A) → list-map id l ≡ l
list-map-id [] = refl
list-map-id (x ∷ l) rewrite (list-map-id l) = refl

list-endofunctor : ∀{ℓ} → Endofunctor {ℓ} List
list-endofunctor = record
  { map = list-map
  ; map-id = funext (list-map id) id list-map-id
  ; map-comp = {!!}
  }
