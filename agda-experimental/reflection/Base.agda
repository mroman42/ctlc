module Base where

  open import Builtin public

  _∧_ : Bool → Bool → Bool
  true ∧ b = b
  false ∧ b = false

  _∨_ : Bool → Bool → Bool
  true ∨ b = true
  false ∨ b = b

  _⇒_ : Bool → Bool → Bool
  true ⇒ b = b
  false ⇒ b = true

  ¬ : Bool → Bool
  ¬ true = false
  ¬ false = true

  data ⊥ : Set where

  Prf : Bool → Set
  Prf true = ⊤
  Prf false = ⊥

  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  open _×_ public

  data Fin : ℕ → Set where
    fzero : {n : ℕ} → Fin (succ n)
    fsuc : {n : ℕ} → Fin n → Fin (succ n)

  data Vector (A : Set) : ℕ → Set where
    [] : Vector A zero
    _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)


