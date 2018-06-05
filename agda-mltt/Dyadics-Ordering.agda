{-# OPTIONS --without-K #-}

-- Agda-MLTT library.
-- Author: Mario Román.

-- Dyadics-Ordering.  Some technical lemmas about order on the dyadic
-- numbers, relating it to ordering on the natural numbers.

module Dyadics-Ordering where

open import Naturals
open import Dyadics

-- Ordering in terms of natural numbers.
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

-- Addition.
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

-- Multiplication.
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

-- All positive dyadic rationals are positive.
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


-- Extract evidence from an ordering relation.
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
        sublemma rewrite
          exp2plus e e'
          | *comm (exp2 e) (exp2 e')
          | *assoc n (exp2 e') (exp2 e)
          | *comm (n * exp2 e') (exp2 e)
          | *comm k (exp2 e)
          | inv (*distr (exp2 e) (n * exp2 e') k)
          | α
          | *assoc (exp2 e) n' (exp2 e)
          | *comm (exp2 e) n'
          | inv (*assoc (n' * exp2 e) (exp2 e) (exp2 e'))
          | inv (exp2plus e e')
          | inv (*assoc n' (exp2 e) (exp2 (e + e')))
          | inv (exp2plus e (e + e'))
          = refl

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
        sublemma rewrite
          exp2plus e e₁
          | *assoc n₁ (exp2 e) (exp2 e₁)
          | *comm (n₁ * exp2 e) (exp2 e₁) 
          | *comm k (exp2 e₁)
          | inv (*distr (exp2 e₁) (n₁ * exp2 e) k)
          | α
          | *comm (exp2 e₁) (n * exp2 e₁)
          | inv (*assoc (n * exp2 e₁) (exp2 e₁) (exp2 e))
          | inv (exp2plus e₁ e)
          | inv (*assoc n (exp2 e₁) (exp2 (e₁ + e)))
          | inv (exp2plus e₁ (e₁ + e))
          | +comm e₁ e
          = refl


-- Lemmas on addition, multiplication and positivity.
+nonzero : (a b : D)
  → zer <d a ≡ true
  → zer <d a +d b ≡ true
+nonzero (dyadic n₁ e₁ x₁) (dyadic n e x) p rewrite
  ltmk 0 0 (n₁ * exp2 e + n * exp2 e₁) (e₁ + e)
  | *runit (n₁ * exp2 e + n * exp2 e₁)
  | *runit n₁
  = <bound+ 0 (n₁ * exp2 e) _ (<bound* zero n₁ (exp2 e) (exp2>zero e) p)

alwayspos : (a : D) → a <d zer ≡ false
alwayspos (dyadic n e x) = refl

<sqbt0 : ∀ c
  → (zer <d c ≡ true)
  → Σ D (λ u → (zer <d u ≡ true) × (u *d u <d c ≡ true))
<sqbt0 (dyadic zero e x) ()
<sqbt0 (dyadic (succ n) e x) p = mkd 1 (succ e) , (refl , lemma e)
  where
    lemma : ∀ e → exp2 e + zero < (succ n) * (exp2 (succ e + succ e)) ≡ true
    lemma e rewrite
      +rzero (exp2 e)
      | *comm (succ n) (exp2 (succ e + succ e))
      | exp2plus e (succ e)
      | inv (*distr (exp2 e) (exp2 (succ e)) (exp2 (succ e)))
      | inv (*runit (exp2 e))
      | inv (*assoc (exp2 e) 1 (exp2 e * 1 + exp2 e * 1 + (exp2 e * 1 + exp2 e * 1)))
      | inv (*assoc (exp2 e) (exp2 e * 1 + exp2 e * 1 + (exp2 e * 1 + exp2 e * 1) + 0) (succ n))
      | <mult-inj 1 ((exp2 e * 1 + exp2 e * 1 + (exp2 e * 1 + exp2 e * 1) + 0) * succ n) (exp2 e) (exp2-notzero e)
      | *runit (exp2 e)
      | +rzero (exp2 e + exp2 e + (exp2 e + exp2 e))
      = sublemma e
      where
        slemma2 : ∀ a b c → 0 < c ≡ true → a < b ≡ true → a < b * c ≡ true
        slemma2 a b zero () q
        slemma2 a b (succ c) p q rewrite
          *comm b (succ c)
          = <bound+ a b (c * b) q
      
        sublemma : ∀ e → 1 < (exp2 (succ e) + exp2 (succ e)) * succ n ≡ true
        sublemma e = slemma2 1 (exp2 e + exp2 e + (exp2 e + exp2 e)) (succ n) refl
          (<bound+ 1 (exp2 e + exp2 e) (exp2 e + exp2 e) (u e))
          where
            u : ∀ e → 1 < exp2 e + exp2 e ≡ true
            u zero = refl
            u (succ e) = <bound+ 1 (exp2 e + exp2 e) (exp2 e + exp2 e) (u e)


-- Technical lemmas on the square root. They will allow us to define
-- the square root on real numbers.
<sqbetween-integers : ∀ n x n' x'
  → dyadic n 0 x <d dyadic n' 0 x' ≡ true
  → Σ D (λ c → ((dyadic n 0 x) <d c *d c ≡ true) × ((dyadic n' 0 x') <d c *d c ≡ false))
<sqbetween-integers n x n' x' p rewrite
  *runit n
  | *runit n'
  with (diffsq n n' p)
... | (m , (d , (u , v))) = mkd d m , (lemma1 , lemma2)
  where
    lemma1 : dyadic n 0 x <d mkd d m *d mkd d m ≡ true
    lemma1 rewrite
      mult-mk d m d m
      | mkd-norm n 0 x
      | ltmk n 0 (d * d) (m + m)
      | *runit (d * d)
      | *comm n (exp2 (m + m))
      | +rzero m
      = u
    lemma2 : dyadic n' 0 x' <d mkd d m *d mkd d m ≡ false
    lemma2 rewrite
      mult-mk d m d m
      | mkd-norm n' 0 x'
      | ltmk n' 0 (d * d) (m + m)
      | *runit (d * d)
      | *comm n' (exp2 (m + m))
      | +rzero m      
      = v  

lemma : ∀ n n₁ e e₁ → n * exp2 e₁ < n₁ * exp2 e ≡ true → 
      exp2 e * exp2 e₁ * exp2 e₁ * n < exp2 e₁ * exp2 e * exp2 e * n₁ ≡ true
lemma n n₁ e e₁ p rewrite
  *comm (exp2 e₁) (exp2 e)
  | inv (*assoc (exp2 e * exp2 e₁) (exp2 e₁) n)
  | inv (*assoc (exp2 e * exp2 e₁) (exp2 e) n₁)
  | inv (*assoc (exp2 e) (exp2 e₁) (exp2 e₁ * n))
  | inv (*assoc (exp2 e) (exp2 e₁) (exp2 e * n₁))
  | <mult-inj (exp2 e₁ * (exp2 e₁ * n)) (exp2 e₁ * (exp2 e * n₁)) (exp2 e) (exp2-notzero e)
  | <mult-inj (exp2 e₁ * n) (exp2 e * n₁) (exp2 e₁) (exp2-notzero e₁)
  | *comm (exp2 e₁) n
  | *comm (exp2 e) n₁ 
  = p      

<sqbetween-almost : (a b : D)
  → a <d b ≡ true
  → Σ D (λ c → (a <d c *d c ≡ true) × (b <d c *d c ≡ false))
<sqbetween-almost (dyadic n e x) (dyadic n₁ e₁ x₁) p
  with diffsq (exp2 e * exp2 e₁ * exp2 e₁ * n) (exp2 e₁ * exp2 e * exp2 e * n₁) (lemma n n₁ e e₁ p)
... | (ec , (c , (α , β))) = mkd c (e + e₁ + ec) , (lemma1 , lemma2)
  where
    lemma1 : dyadic n e x <d mkd c (e + e₁ + ec) *d mkd c (e + e₁ + ec) ≡ true
    lemma1 rewrite
      mult-mk c (e + e₁ + ec) c (e + e₁ + ec)
      | mkd-norm n e x
      | ltmk n e (c * c) (e + e₁ + ec + (e + e₁ + ec))
      | +rzero ec
      | *comm n (exp2 (e + e₁ + ec + (e + e₁ + ec)))
      | *comm (c * c) (exp2 e)
      | inv (+assoc e e₁ ec)
      | inv (+assoc e (e₁ + ec) (e + (e₁ + ec)))
      | exp2plus e (e₁ + ec + (e + (e₁ + ec)))
      | inv (*assoc (exp2 e) (exp2 (e₁ + ec + (e + (e₁ + ec)))) n)
      | <mult-inj (exp2 (e₁ + ec + (e + (e₁ + ec))) * n) (c * c) (exp2 e) (exp2-notzero e)
      | +comm e₁ ec
      | +assoc e ec e₁
      | +comm e ec
      | inv (+assoc ec e₁ (ec + e + e₁))
      | +comm e₁ (ec + e + e₁)
      | inv (+assoc (ec + e) e₁ e₁)
      | inv (+assoc ec e (e₁ + e₁))
      | +assoc ec ec (e + (e₁ + e₁))
      | exp2plus (ec + ec) (e + (e₁ + e₁))
      | exp2plus e (e₁ + e₁)
      | exp2plus e₁ e₁
      | *assoc (exp2 e) (exp2 e₁)  (exp2 e₁)
      | inv (*assoc (exp2 (ec + ec)) (exp2 e * exp2 e₁ * exp2 e₁) n)
      = α
    lemma2 : dyadic n₁ e₁ x₁ <d mkd c (e + e₁ + ec) *d mkd c (e + e₁ + ec) ≡ false
    lemma2 rewrite
      mult-mk c (e + e₁ + ec) c (e + e₁ + ec)
      | mkd-norm n₁ e₁ x₁
      | ltmk n₁ e₁ (c * c) (e + e₁ + ec + (e + e₁ + ec))
      | +comm e e₁
      | inv (+assoc (e₁ + e) ec (e₁ + e + ec))
      | inv (+assoc e₁ e (ec + (e₁ + e + ec)))
      | exp2plus e₁ (e + (ec + (e₁ + e + ec)))
      | *assoc n₁ (exp2 e₁) (exp2 (e + (ec + (e₁ + e + ec))))
      | *comm n₁ (exp2 e₁)
      | *comm (c * c) (exp2 e₁)
      | inv (*assoc (exp2 e₁) n₁ (exp2 (e + (ec + (e₁ + e + ec)))))
      | <mult-inj (n₁ * exp2 (e + (ec + (e₁ + e + ec)))) (c * c) (exp2 e₁) (exp2-notzero e₁)
      | *comm n₁ (exp2 (e + (ec + (e₁ + e + ec))))
      | +comm (e₁ + e) ec
      | +assoc ec ec (e₁ + e)
      | +assoc e (ec + ec)  (e₁ + e)
      | +comm e (ec + ec)
      | inv (+assoc (ec + ec) e (e₁ + e))
      | exp2plus (ec + ec) (e + (e₁ + e))
      | +assoc e e₁ e
      | +comm e e₁
      | exp2plus (e₁ + e) e
      | exp2plus e₁ e
      | +rzero ec
      | *assoc (exp2 (ec + ec)) (exp2 e₁ * exp2 e * exp2 e) n₁
      = β


    
