-- http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.722.6833&rep=rep1&type=pdf

-- open import Agda.Builtin.Reflection

open import Base

module Naturals where

  module Even where
  
    _+_ : ℕ → ℕ → ℕ
    zero + b = b
    succ a + b = succ (a + b)
  
    data Even : ℕ → Set where
      isEven0 : Even 0
      isEven+2 : {n : ℕ} → Even n → Even (2 + n)
  
    even? : ℕ → Set
    even? 0 = ⊤
    even? 1 = ⊥
    even? (succ (succ n)) = even? n
  
    soundnessEven : {n : ℕ} → even? n → Even n
    soundnessEven {0} _ = isEven0
    soundnessEven {succ zero} ()
    soundnessEven {succ (succ n)} p = isEven+2 (soundnessEven p)
    
    isEven8772 : Even 8772
    isEven8772 = soundnessEven **
  

  module Tautologies where


    
    data Fin : ℕ → Set where
      fzero : {n : ℕ} → Fin (succ n)
      fsucc : {n : ℕ} → Fin n → Fin (succ n)
      
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
      _∷_ : {n : ℕ} → Bool → Env n → Env (succ n)

    lookup : {n : ℕ} → Fin n → Env n → Bool
    lookup {zero} () e
    lookup {succ n} fzero (x ∷ e) = x
    lookup {succ n} (fsucc f) (x ∷ e) = lookup f e

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
      step : {n m : ℕ} → Diff (succ n) m → Diff n m

    coerceDiff : {n m : ℕ} → Diff n m → Diff (succ n) (succ m)
    coerceDiff base = base
    coerceDiff (step p) = step (coerceDiff p)

    diff0 : {m : ℕ} → Diff 0 m
    diff0 {zero} = base
    diff0 {succ m} = step (coerceDiff diff0)

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
    soundnessAcc b acc (step d) p true = soundnessAcc b (true ∷ acc) d (fst p)
    soundnessAcc b acc (step d) p false = soundnessAcc b (false ∷ acc) d (snd p)

    soundness : {n : ℕ} → (b : BoolExpr n) → {p : foralls b} → proofGoal diff0 b []
    soundness {n} b {p} = soundnessAcc b [] diff0 p

--    macro
--      tautology : Term → TC T
--      tautology = ?
