open import base.Base

-- Cite:
--  Agda reflection module
--  Swiestra on reflection

module FromHaskell where

-- Language:
-- 
--   1. Natural equalities:
--        (a : Nat) zero succ + * ≡?
--   2. Natural inequalities
--        (a : Nat) <?
--

-- Desired usage:
--
--   asdf a b c constr1 constr2 = lorem ipsum {?}
--   asdf a b c constr1 constr2 = lorem ipsum (solveBy [constr1 , constr2] for [a , b , c])
--
--  It must prove absurd statements!!!
--    assume(q > 0)
--    assume(q > 1)
--    ValueError: Assumption is inconsistent
-- 

-- Sage
-- 

data NatExpr (n : Nat) : Set where
  Var : Nat → NatExpr n
  Zero : NatExpr n
  Suc : NatExpr n → NatExpr n
  Add : NatExpr n → NatExpr n → NatExpr n
  Mult : NatExpr n → NatExpr n → NatExpr n

data NatStatement (n : Nat) : Set where
  Equal : NatExpr n → NatExpr n → NatStatement n
  Less : NatExpr n → NatExpr n → NatStatement n

record NatProblem (n : Nat) : Set where
  field
    constraints : List (NatStatement n)
    goal        : NatStatement n


Env : Nat → Set
Env = Vector Nat

lookup : {n : Nat} → Nat → Env n → Nat
lookup m [] = 0
lookup zero (x ∷ env) = x
lookup (suc m) (x ∷ env) = lookup m env

⟦_⊦_⟧ₙ : {n : Nat} (e : Env n) → NatExpr n → Nat
⟦ env ⊦ Var x ⟧ₙ = lookup x env
⟦ env ⊦ Zero ⟧ₙ = 0
⟦ env ⊦ Suc a ⟧ₙ = suc ⟦ env ⊦ a ⟧ₙ
⟦ env ⊦ Add a b ⟧ₙ = ⟦ env ⊦ a ⟧ₙ + ⟦ env ⊦ b ⟧ₙ
⟦ env ⊦ Mult a b ⟧ₙ = ⟦ env ⊦ a ⟧ₙ * ⟦ env ⊦ b ⟧ₙ

⟦_⊦_⟧ₛ : {n : Nat} (e : Env n) → NatStatement n → Bool
⟦ env ⊦ Equal a b ⟧ₛ = ⟦ env ⊦ a ⟧ₙ == ⟦ env ⊦ b ⟧ₙ
⟦ env ⊦ Less a b ⟧ₛ = ⟦ env ⊦ a ⟧ₙ < ⟦ env ⊦ b ⟧ₙ



proofGoal : {n : Nat} → Env n → NatStatement n → Set
proofGoal [] st = {!!}
proofGoal (x ∷ env) st = {!!}


-- macro
--   by-magic : Term → TC ⊤
--   by-magic hole =
--     bindTC (inferType hole) λ goal →
--     unify hole (magic goal)

infix 5 _≡?_ 
_≡?_ : Nat → Nat → Bool
zero ≡? zero = true
zero ≡? suc b = false
suc a ≡? zero = false
suc a ≡? suc b = a ≡? b

postulate
  asdfs : ∀ a b → (a + b ≡? b + a) ≡ true

asdf : ∀ a b → (a + b ≡? b + a) ≡ true
asdf a b = {!!}
  

macro
  translate : Term → Term → TC ⊤
  translate t hole = {!!}

solver : {n : Nat} → NatStatement n → Bool
solver a = true

-- postulate
--   solversoundness : {n : Nat} → (expr : NatStatement n) → ⟦ expr ⟧ ≡ solver expr


