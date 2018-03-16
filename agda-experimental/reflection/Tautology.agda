open import Base

module Tautology where

  data BoolExpr (n : ℕ) : Set where
    Truth : BoolExpr n
    Falsehood : BoolExpr n
    And : BoolExpr n → BoolExpr n → BoolExpr n
    Or : BoolExpr n → BoolExpr n → BoolExpr n
    Imp : BoolExpr n → BoolExpr n → BoolExpr n
    Not : BoolExpr n → BoolExpr n
    Atomic : Fin n → BoolExpr n

  Env : ℕ → Set
  Env = Vector Bool

  lookup : {n : ℕ} → Fin n → Env n → Bool
  lookup {zero} () e
  lookup {succ n} fzero (x ∷ e) = x
  lookup {succ n} (fsuc f) (x ∷ e) = lookup f e


  ⟦_⊦_⟧ : {n : ℕ} (e : Env n) → BoolExpr n → Bool
  ⟦ env ⊦ Truth ⟧ = true
  ⟦ env ⊦ Falsehood ⟧ = false
  ⟦ env ⊦ And t t₁ ⟧ = ⟦ env ⊦ t ⟧ ∧ ⟦ env ⊦ t₁ ⟧
  ⟦ env ⊦ Or t t₁ ⟧ = ⟦ env ⊦ t ⟧ ∨ ⟦ env ⊦ t₁ ⟧
  ⟦ env ⊦ Imp t t₁ ⟧ = ⟦ env ⊦ t ⟧ ⇒ ⟦ env ⊦ t₁ ⟧ 
  ⟦ env ⊦ Not t ⟧ = ¬ ⟦ env ⊦ t ⟧
  ⟦ env ⊦ Atomic x ⟧ = lookup x env

  data Diff : ℕ → ℕ → Set where
    base : {n : ℕ} → Diff n n
    step : {n m : ℕ} → Diff (succ n) m → Diff n m

  coerceDiff : {n m : ℕ} → Diff n m → Diff (succ n) (succ m)
  coerceDiff base = base
  coerceDiff (step p) = step (coerceDiff p)

  diff0 : {m : ℕ} → Diff zero m
  diff0 {zero} = base
  diff0 {succ m} = step (coerceDiff diff0)


  forallsAcc : {n m : ℕ} → BoolExpr m → Env n → Diff n m → Set
  forallsAcc b acc base = Prf ⟦ acc ⊦ b ⟧
  forallsAcc b acc (step y) = forallsAcc b (true ∷ acc) y × forallsAcc b (false ∷ acc) y

  foralls : {m : ℕ} → BoolExpr m → Set
  foralls {m} b = forallsAcc b [] diff0

  proofGoal : {n m : ℕ} → Diff n m → BoolExpr m → Env n → Set
  proofGoal base b acc = Prf ⟦ acc ⊦ b ⟧
  proofGoal (step p) b acc = (a : Bool) → proofGoal p b (a ∷ acc)

  soundnessAcc : {n m : ℕ} → (b : BoolExpr m) → (env : Env n) → (d : Diff n m) →
                 forallsAcc b env d → proofGoal d b env
  soundnessAcc b acc base p = p
  soundnessAcc b acc (step d) p true = soundnessAcc b (true ∷ acc) d (fst p)
  soundnessAcc b acc (step d) p false = soundnessAcc b (false ∷ acc) d (snd p)

  soundness : {n : ℕ} → (b : BoolExpr n) → {p : foralls b} → proofGoal diff0 b []
  soundness {n} b {p} = soundnessAcc b [] diff0 p


  -- Testing
  test : Prf true
  test = soundness {0} (Truth)

  test2 : (a : Bool) → Prf (a ∨ true)
  test2 = soundness {1} (Or (Atomic fzero) Truth)

  test3 : (a : Bool) → Prf (a ⇒ true)
  test3 = soundness {1} (Imp (Atomic fzero) Truth)
 
  test4 : (a b : Bool) → Prf (a ∨ (¬ a))
  test4 = soundness {2} (Or (Atomic (fsuc fzero)) (Not (Atomic (fsuc fzero))))


  -- Macros
  macro
    boolToExpr : Term → Term → TC ⊤
    boolToExpr (def (quote _∧_) (a ∷ b ∷ [])) hole = unify hole (con (quote And) (a ∷ b ∷ []))
    boolToExpr (def (quote _∨_) (a ∷ b ∷ [])) hole = unify hole (con (quote Or) (a ∷ b ∷ []))
    boolToExpr (def (quote _⇒_) (a ∷ b ∷ [])) hole = unify hole (con (quote Imp) (a ∷ b ∷ []))
    boolToExpr (def (quote ¬) (a ∷ [])) hole = unify hole (con (quote Not) (a ∷ []))
    boolToExpr (con (quote true) ([])) hole = unify hole (con (quote Truth) ([]))
    boolToExpr (con (quote false) ([])) hole = unify hole (con (quote Falsehood) ([]))    
    {-# CATCHALL #-}
    boolToExpr v hole = unify hole v

  elem? : ℕ → List (Arg Term) → Arg Term
  elem? n [] = arg (arg-info visible relevant) unknown
  elem? zero (x ∷ l) = x
  elem? (succ n) (x ∷ l) = elem? n l

  countingPi : List (Arg Term) → Type → Term
  countingPi l (pi a (abs s x)) = countingPi (a ∷ l) x
  countingPi l (var n []) = con (quote Atomic) (elem? n l ∷ [])
  countingPi l (def (quote _∧_) (a ∷ b ∷ [])) = (con (quote And) (a ∷ b ∷ []))
  countingPi l (def (quote _∨_) (a ∷ b ∷ [])) = (con (quote Or) (a ∷ b ∷ []))
  countingPi l (def (quote _⇒_) (a ∷ b ∷ [])) = (con (quote Imp) (a ∷ b ∷ []))
  countingPi l (def (quote ¬) (a ∷ [])) = (con (quote Not) (a ∷ []))
  countingPi l (con (quote true) []) = (con (quote Truth) ([]))
  countingPi l (con (quote false) []) = (con (quote Falsehood) ([]))
  {-# CATCHALL #-}
  countingPi l t = t

  

  macro
    by-tautology : Term → TC ⊤
    by-tautology hole = 
      bindTC (inferType hole) λ goal →
      unify hole {!!}

  macro
    plus-to-times : Term → Term → TC ⊤
    plus-to-times (def (quote _+_) (a ∷ b ∷ [])) hole = unify hole (def (quote _*_) (a ∷ b ∷ []))
    {-# CATCHALL #-}
    plus-to-times v hole = unify hole v

  thm : (c d : ℕ) → plus-to-times (c + d) ≡ c * d
  thm a b = refl

  test5 : Prf true
  test5 = soundness {0} (boolToExpr true)

  test6 : (a : Bool) → Prf (a ∨ true)
  test6 = {!!}
