module Stlc where

-- Dependently typed metaprogramming in Agda.


-- Syntax.
data Type : Set where
  ⊤ : Type
  _×_ : Type → Type → Type
  _⊃_ : Type → Type → Type
infix 5 _⊃_
infix 6 _×_

data Ctx : Set where
  • : Ctx
  _,_ : Ctx → Type → Ctx

data _∈_ (τ : Type) : Ctx → Set where
  fzer : ∀ {Γ} → τ ∈ Γ , τ
  fsuc : ∀ {Γ σ} → τ ∈ Γ → τ ∈ Γ , σ
infix 3 _∈_


data _⊦_ (Γ : Ctx) : Type → Set where
  var : ∀ {τ}
    → τ ∈ Γ
    ---------
    → Γ ⊦ τ

  unit :
  
    ----------
      Γ ⊦ ⊤

  lam : ∀ {σ τ}
    → Γ , σ ⊦ τ
    ------------
    → Γ ⊦ σ ⊃ τ

  app : ∀ {σ τ}
    → Γ ⊦ σ ⊃ τ
    → Γ ⊦ σ
    -------------
    → Γ ⊦ τ

  fst : ∀ {σ τ}
    → Γ ⊦ σ × τ
    ------------
    → Γ ⊦ σ

  snd : ∀ {σ τ}
    → Γ ⊦ σ × τ
    ------------
    → Γ ⊦ τ

  pair : ∀ {σ τ}
    → Γ ⊦ σ
    → Γ ⊦ τ
    -------------
    → Γ ⊦ σ × τ
infix 3 _⊦_

cut-elimination : {Γ : Ctx} {σ τ : Type} → Γ ⊦ σ → Γ , σ ⊦ τ → Γ ⊦ τ
cut-elimination (var fzer) (var fzer) = var fzer
cut-elimination (var fzer) (var (fsuc x)) = var x
cut-elimination (var fzer) unit = unit
cut-elimination (var fzer) (lam b) = {!!}
cut-elimination (var fzer) (app b b₁) = {!!}
cut-elimination (var fzer) (fst b) = {!!}
cut-elimination (var fzer) (snd b) = {!!}
cut-elimination (var fzer) (pair b b₁) = {!!}
cut-elimination (var (fsuc x)) b = {!!}
cut-elimination unit b = {!!}
cut-elimination (lam a) b = {!!}
cut-elimination (app a a₁) b = {!!}
cut-elimination (fst a) b = {!!}
cut-elimination (snd a) b = {!!}
cut-elimination (pair a a₁) b = {!!}


normalize : {Γ : Ctx} {τ : Type} → Γ ⊦ τ → Γ ⊦ τ
normalize {Γ} {τ} (fst (pair a _)) = normalize a
normalize {Γ} {τ} (snd (pair _ b)) = normalize b
normalize {Γ} {τ} (app (lam b) a) = {!!}
normalize {Γ} {τ} (fst m) = fst (normalize m)
normalize {Γ} {τ} (snd m) = snd (normalize m)
normalize {Γ} {τ} (app p a) = app (normalize p) (normalize a)
normalize {Γ} {τ} t = t
