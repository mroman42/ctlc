module Base where

  data ⊤ : Set where
    ** : ⊤
  
  data ⊥ : Set where
  
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}  

  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  open _×_ public

  data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A

  data Bool : Set where
    true : Bool
    false : Bool

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
