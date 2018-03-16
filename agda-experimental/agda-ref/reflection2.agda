-- open import Agda.Reflection

module reflection2 where

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

  record ⊤ : Set where
    constructor tt

  data ⊥ : Set where

  Prf : Bool → Set
  Prf true = ⊤
  Prf false = ⊥

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}

  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B

  fst : {A B : Set} → A × B → A
  fst (a , b) = a

  snd : {A B : Set} → A × B → B
  snd (a , b) = b

  data Fin : ℕ → Set where
    fzero : {n : ℕ} → Fin (succ n)
    fsuc : {n : ℕ} → Fin n → Fin (succ n)

  data BoolExpr (n : ℕ) : Set where
    Truth : BoolExpr n
    Falsehood : BoolExpr n
    And : BoolExpr n → BoolExpr n → BoolExpr n
    Or : BoolExpr n → BoolExpr n → BoolExpr n
    Imp : BoolExpr n → BoolExpr n → BoolExpr n
    Not : BoolExpr n → BoolExpr n
    Atomic : Fin n → BoolExpr n

  data Env : ℕ → Set where
    [] : Env zero
    _∷_ : {n : ℕ} → Bool → Env n → Env (succ n)

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
 
  test4 : (a : Bool) → (b : Bool) → Prf (a ∨ (¬ a))
  test4 = soundness {2} (Or (Atomic (fsuc fzero)) (Not (Atomic (fsuc fzero))))


  -- Macros
  
