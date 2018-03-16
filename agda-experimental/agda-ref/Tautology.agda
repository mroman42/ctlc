open import Data.Nat
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Relation.Binary.PropositionalEquality

module Tautology where

  _⇒_ : Bool → Bool → Bool
  true ⇒ b = b
  false ⇒ b = true

  ¬ : Bool → Bool
  ¬ true = false
  ¬ false = true

  data Fin : ℕ → Set where
    fzero : {n : ℕ} → Fin (suc n)
    fsuc : {n : ℕ} → Fin n → Fin (suc n)
      
  data BoolExpr (n : ℕ) : Set where
    Truth : BoolExpr n
    Falsehood : BoolExpr n
    And : BoolExpr n → BoolExpr n → BoolExpr n
    Or : BoolExpr n → BoolExpr n → BoolExpr n
    Imp : BoolExpr n → BoolExpr n → BoolExpr n
    Not : BoolExpr n → BoolExpr n
    Atomic : Fin n → BoolExpr n

  data Env : ℕ → Set where
    [] : Env 0
    _∷_ : {n : ℕ} → Bool → Env n → Env (suc n)

  lookup : {n : ℕ} → Fin n → Env n → Bool
  lookup {zero} () e
  lookup {suc n} fzero (x ∷ e) = x
  lookup {suc n} (fsuc f) (x ∷ e) = lookup f e

  ⟦_⊦_⟧ : {n : ℕ} (e : Env n) → BoolExpr n → Bool
  ⟦ env ⊦ Truth ⟧ = true
  ⟦ env ⊦ Falsehood ⟧ = false
  ⟦ env ⊦ And t t₁ ⟧ = ⟦ env ⊦ t ⟧ ∧ ⟦ env ⊦ t₁ ⟧
  ⟦ env ⊦ Or t t₁ ⟧ = ⟦ env ⊦ t ⟧ ∨ ⟦ env ⊦ t₁ ⟧
  ⟦ env ⊦ Imp t t₁ ⟧ = ⟦ env ⊦ t ⟧ ⇒ ⟦ env ⊦ t₁ ⟧ 
  ⟦ env ⊦ Not t ⟧ = ¬ ⟦ env ⊦ t ⟧
  ⟦ env ⊦ Atomic x ⟧ = lookup x env
    
  P : Bool → Set
  P true = ⊤
  P false = ⊥

  data Diff : ℕ → ℕ → Set where
    base : {n : ℕ} → Diff n n
    step : {n m : ℕ} → Diff (suc n) m → Diff n m

  coerceDiff : {n m : ℕ} → Diff n m → Diff (suc n) (suc m)
  coerceDiff base = base
  coerceDiff (step p) = step (coerceDiff p)

  diff0 : {m : ℕ} → Diff 0 m
  diff0 {zero} = base
  diff0 {suc m} = step (coerceDiff diff0)

  forallsAcc : {n m : ℕ} → BoolExpr m → Env n → Diff n m → Set
  forallsAcc b acc base = P ⟦ acc ⊦ b ⟧
  forallsAcc b acc (step y) = forallsAcc b (true ∷ acc) y × forallsAcc b (false ∷ acc) y

  foralls : {m : ℕ} → BoolExpr m → Set
  foralls {m} b = forallsAcc b [] diff0

  proofGoal : {n m : ℕ} → Diff n m → BoolExpr m → Env n → Set
  proofGoal base b acc = P ⟦ acc ⊦ b ⟧
  proofGoal (step p) b acc = (a : Bool) → proofGoal p b (a ∷ acc)

  soundnessAcc : {n m : ℕ} → (b : BoolExpr m) → (env : Env n) → (d : Diff n m) →
                 forallsAcc b env d → proofGoal d b env
  soundnessAcc b acc base p = p
  soundnessAcc b acc (step d) p true = soundnessAcc b (true ∷ acc) d (proj₁ p)
  soundnessAcc b acc (step d) p false = soundnessAcc b (false ∷ acc) d (proj₂ p)

  soundness : {n : ℕ} → (b : BoolExpr n) → {p : foralls b} → proofGoal diff0 b []
  soundness {n} b {p} = soundnessAcc b [] diff0 p



  asf : (a : Bool) → P (a ∨ true)
  asf = soundness (Or (Atomic fzero) Truth)

  -- macro
  -- termToBoolExpr : Term → BoolExpr 1
  -- termToBoolExpr t = {!!}
  -- termToBoolExpr (var x args) = {!!}
  -- termToBoolExpr (con c args) = {!!}
  -- termToBoolExpr (def f args) = {!!}
  -- termToBoolExpr (lam v t) = {!!}
  -- termToBoolExpr (pat-lam cs args) = {!!}
  -- termToBoolExpr (pi a b) = {!!}
  -- termToBoolExpr (agda-sort s) = {!!}
  -- termToBoolExpr (lit l) = {!!}
  -- termToBoolExpr (meta x x₁) = {!!}
  -- termToBoolExpr unknown = {!!}
