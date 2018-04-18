module Dyadics-Ordering where

open import Naturals
open import Dyadics


ltmk : (n e n' e' : ℕ) → (mkd n e) <d (mkd n' e') ≡ n * exp2 e' < n' * exp2 e
ltmk n e n' e' with mk-const n e | mk-const n' e'
ltmk n e n' e' | k , (α , (β , γ)) | k' , (α' , (β' , γ')) rewrite
  lt$ (mkd n e) (mkd n' e')
  | inv (<mult-inj
    (num$ (mkd n e) * exp2 (pow$ (mkd n' e')))
    (num$ (mkd n' e') * exp2 (pow$ (mkd n e)))
    k α)
  | *assoc k (num$ (mkd n e)) (exp2 (pow$ (mkd n' e')))
  | inv β
  | *assoc k (num$ (mkd n' e')) (exp2 (pow$ (mkd n e)))
  | *comm k (num$ (mkd n' e'))
  | inv (*assoc (num$ (mkd n' e')) k (exp2 (pow$ (mkd n e))))
  | inv γ
  | inv (<mult-inj (n * exp2 (pow$ (mkd n' e'))) (num$ (mkd n' e') * exp2 e) k' α')
  | *assoc k' n (exp2 (pow$ (mkd n' e')))
  | *comm k' n
  | inv (*assoc n k' (exp2 (pow$ (mkd n' e'))))
  | inv γ'
  | *assoc k' (num$ (mkd n' e')) (exp2 e)
  | inv β'
  = refl

ltplus : (a b c : D) → (a +d b) <d (a +d c) ≡ b <d c
ltplus (dyadic n e x) (dyadic n₁ e₁ x₁) (dyadic n₂ e₂ x₂) rewrite
  ltmk (n * exp2 e₁ + n₁ * exp2 e) (e + e₁) (n * exp2 e₂ + n₂ * exp2 e) (e + e₂)
  | *comm (n * exp2 e₁ + n₁ * exp2 e) (exp2 (e + e₂))
  | *comm (n * exp2 e₂ + n₂ * exp2 e) (exp2 (e + e₁))
  | *distr (exp2 (e + e₂)) (n * exp2 e₁) (n₁ * exp2 e)
  | *distr (exp2 (e + e₁)) (n * exp2 e₂) (n₂ * exp2 e)
  | *comm n (exp2 e₁)
  | *comm n (exp2 e₂)
  | *assoc (exp2 (e + e₂)) (exp2 e₁) n
  | *assoc (exp2 (e + e₁)) (exp2 e₂) n
  | inv (exp2plus (e + e₁) e₂)
  | inv (exp2plus (e + e₂) e₁)
  | inv (+assoc e e₂ e₁)  
  | +comm e₂ e₁
  | (+assoc e e₁ e₂)
  | *comm n₁ (exp2 e)
  | *comm n₂ (exp2 e)
  | exp2plus e e₂
  | exp2plus e e₁
  | inv (*assoc (exp2 e) (exp2 e₂) (exp2 e * n₁))
  | inv (*assoc (exp2 e) (exp2 e₁) (exp2 e * n₂))
  | *assoc (exp2 e₂) (exp2 e) n₁
  | *assoc (exp2 e₁) (exp2 e) n₂
  | *comm (exp2 e₂) (exp2 e)
  | *comm (exp2 e₁) (exp2 e)
  | <plus (exp2 (e + e₁ + e₂) * n) (exp2 e * (exp2 e * exp2 e₂ * n₁)) (exp2 e * (exp2 e * exp2 e₁ * n₂))
  | <mult-inj (exp2 e * exp2 e₂ * n₁)  (exp2 e * exp2 e₁ * n₂) (exp2 e) (exp2-notzero e)
  | inv (*assoc (exp2 e) (exp2 e₂) n₁)
  | inv (*assoc (exp2 e) (exp2 e₁) n₂)  
  | <mult-inj (exp2 e₂ * n₁)  (exp2 e₁ * n₂) (exp2 e) (exp2-notzero e)
  | *comm (exp2 e₂) n₁
  | *comm (exp2 e₁) n₂
  = refl

ltmult : (a b c : D) → zer <d a ≡ true → (a *d b) <d (a *d c) ≡ b <d c
ltmult (dyadic n e x) (dyadic n₁ e₁ x₁) (dyadic n₂ e₂ x₂) p rewrite
  *runit n
  | ltmk (n * n₁) (e + e₁) (n * n₂) (e + e₂)
  | exp2plus e e₂
  | exp2plus e e₁
  | inv (*assoc n n₁ (exp2 e * exp2 e₂))
  | inv (*assoc n n₂ (exp2 e * exp2 e₁))
  | *assoc n₁ (exp2 e) (exp2 e₂)
  | *assoc n₂ (exp2 e) (exp2 e₁)
  | *comm n₁ (exp2 e)
  | *comm n₂ (exp2 e)
  | <mult-inj (exp2 e * n₁ * exp2 e₂) (exp2 e * n₂ * exp2 e₁) n (<iszero n p)
  | inv (*assoc (exp2 e) n₁ (exp2 e₂))
  | inv (*assoc (exp2 e) n₂ (exp2 e₁))  
  | <mult-inj (n₁ * exp2 e₂) (n₂ * exp2 e₁) (exp2 e) (exp2-notzero e)
  = refl

dpositivity : (a b : D) → zer <d a ≡ true → zer <d (a +d b) ≡ true
dpositivity (dyadic n e x) (dyadic n₁ e₁ x₁) p
  rewrite
    mkd-norm 0 0 refl
    | ltmk 0 0 (n * exp2 e₁ + n₁ * exp2 e) (e + e₁)
    | *runit (n * exp2 e₁ + n₁ * exp2 e)
    | *runit n
    = iszero< (n * exp2 e₁ + n₁ * exp2 e)
       (iszero-not-plus-r (n * exp2 e₁) (n₁ * exp2 e)
         (iszero-not-mult n (exp2 e₁) (<iszero n p) (exp2-notzero e₁)))

postulate
  ADMITTED : {A : Set} → A


ltevd : (a b : D) → a <d b ≡ true → Σ D (λ c → (a +d c ≡ b) × (zer <d c ≡ true))
ltevd (dyadic n e x) (dyadic n' e' x') p with <evd (n * exp2 e') (n' * exp2 e) p
... | k , (α , β) = mkd k (e + e') , (lemma , lemma2)
  where
    lemma : dyadic n e x +d mkd k (e + e') ≡ dyadic n' e' x'
    lemma rewrite
      mkd-norm n e x
      | add-mk n e k (e + e')
      | mkd-norm n' e' x'
      = dmk≡ (n * exp2 (e + e') + k * exp2 e) (e + (e + e')) n' e' sublemma
      where
        sublemma : (n * exp2 (e + e') + k * exp2 e) * exp2 e' ≡ n' * exp2 (e + (e + e'))
        sublemma = ADMITTED

    lemma2 : dyadic 0 0 refl <d mkd k (e + e') ≡ true
    lemma2 rewrite ltmk 0 0 k (e + e') | *runit k = β

leevd : (a b : D) → a <d b ≡ false → Σ D (λ c → b +d c ≡ a)
leevd (dyadic n e x) (dyadic n₁ e₁ x₁) p with <nevd (n * exp2 e₁) (n₁ * exp2 e) p
... | k , α = mkd k (e + e₁) , lemma
  where
    lemma : dyadic n₁ e₁ x₁ +d mkd k (e + e₁) ≡ dyadic n e x
    lemma rewrite
      mkd-norm n₁ e₁ x₁
      | add-mk n₁ e₁ k (e + e₁)
      | mkd-norm n e x
      = dmk≡ (n₁ * exp2 (e + e₁) + k * exp2 e₁) (e₁ + (e + e₁)) n e sublemma
      where
        sublemma : (n₁ * exp2 (e + e₁) + k * exp2 e₁) * exp2 e ≡ n * exp2 (e₁ + (e + e₁))
        sublemma = ADMITTED


+nonzero : (a b : D)
  → zer <d a ≡ true
  → zer <d a +d b ≡ true
+nonzero (dyadic n₁ e₁ x₁) (dyadic n e x) p rewrite
  ltmk 0 0 (n₁ * exp2 e + n * exp2 e₁) (e₁ + e)
  | *runit (n₁ * exp2 e + n * exp2 e₁)
  | *runit n₁
  = ADMITTED
