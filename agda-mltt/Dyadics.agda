{-# OPTIONS --without-K #-}

-- Agda-MLTT library.
-- Author: Mario Román.

-- Dyadics.  Dyadic positive rational numbers as a quotient on pairs
-- of natural numbers.

module Dyadics where

open import Naturals

-- A symbolic fraction given as (n/2ᵉ) is normalized if the exponent
-- on the denominator is zero or if the numerator is odd.
normalized : ℕ → ℕ → Bool
normalized n e = or (odd n) (iszero e)

-- We prove that some fractions are automatically normalized.
iszero-normalized : (n e : ℕ) → iszero e ≡ true → normalized n e ≡ true
iszero-normalized n e p rewrite p | or-rtrue (odd n) = refl

odd-normalized : (n e : ℕ) → odd n ≡ true → normalized n e ≡ true
odd-normalized n e p rewrite p = refl

nonzero-normalized : (n e : ℕ) → normalized n (succ e) ≡ true → odd n ≡ true
nonzero-normalized n e p rewrite or-rfalse (odd n) | p = refl

nonzero-normalized2 : (n e : ℕ) → normalized n (succ e) ≡ true → iszero n ≡ false
nonzero-normalized2 zero e p rewrite or-rfalse (odd zero) | p = refl
nonzero-normalized2 (succ n) e p = refl


-- A dyadic rational is a pair of natural numbers describing a
-- normalized fraction.
data D : Set where
  dyadic : (n e : ℕ) → normalized n e ≡ true → D

-- Getters for the numerator and the denominator
num$ : D → ℕ
num$ (dyadic n _ _) = n

pow$ : D → ℕ
pow$ (dyadic _ e _) = e


-- Reflexivity for fractions follows from reflexivity of their
-- components.
drefl : ∀ {n} {e} 
  → {p : normalized n e ≡ true}
  → {q : normalized n e ≡ true}
  ------------------------------
  → dyadic n e p ≡ dyadic n e q
drefl {n} {e} {p} {q} rewrite (uip p q) = refl

drefl-app : (n e n' e' : ℕ)
  → n ≡ n'
  → e ≡ e'
  → {p : normalized n e ≡ true}
  → {q : normalized n' e' ≡ true}
  -------------------------------
  → dyadic n e p ≡ dyadic n' e' q
drefl-app n e n' e' a b {p} {q} rewrite a | b | uip p q = refl

-- Cross multiplication being equal implies equality of the two
-- fractions. This proof employs some lemmas on ordering,
-- exponentiation and parity.
drefl' : ∀ a b → num$ a * exp2 (pow$ b) ≡ num$ b * exp2 (pow$ a) → a ≡ b
drefl' (dyadic n zero x) (dyadic n' zero x') p rewrite *runit n | *runit n' | p = drefl
drefl' (dyadic n zero x) (dyadic n' (succ e') x') p rewrite *runit n' | inv p = exfalso (refute n e' x')
  where
    refute : (m e' : ℕ) → or (odd (m * (exp2 e' + exp2 e'))) false ≡ true → ⊥
    refute n e p rewrite notodd*a+b n (exp2 e) = true≢false (inv p)
drefl' (dyadic n (succ e) x) (dyadic n' zero x') p rewrite *runit n | p = exfalso (refute n' e x)
  where
    refute : (m e' : ℕ) → or (odd (m * (exp2 e' + exp2 e'))) false ≡ true → ⊥
    refute n e p rewrite notodd*a+b n (exp2 e) = true≢false (inv p)
drefl' (dyadic n (succ e) x) (dyadic n' (succ e') x') p = drefl-app n (succ e) n' (succ e') lemma1 (lemma2 p)
  where
    lemma1 : n ≡ n'
    lemma1 = exp2-odd-div n n' (succ e') (succ e) (nonzero-normalized n e x) (nonzero-normalized n' e' x') p

    nonzero-n : iszero n ≡ false
    nonzero-n = nonzero-normalized2 n zero x
    
    lemma2 : n * (exp2 e' + exp2 e') ≡ n' * (exp2 e + exp2 e) → succ e ≡ succ e'
    lemma2 p rewrite inv lemma1 = inv (exp2-inj (succ e') (succ e) (*inj n (exp2 (succ e')) _ nonzero-n p))

d≡ : ∀ {a} {b} → num$ a * exp2 (pow$ b) ≡ num$ b * exp2 (pow$ a) → a ≡ b
d≡ {a} {b} p = drefl' a b p

-- Creates a dyadic rational from a (not necessarily normalized)
-- fraction of given by two natural numbersr.
mkd : ℕ → ℕ → D
mkd n zero = dyadic n 0 (or-rtrue (odd n))
mkd n (succ e) with (odd n)??
mkd n (succ e) | inl x = dyadic n (succ e) (odd-normalized n (succ e) x)
mkd n (succ e) | inr x with (not-odd-form n x)
mkd n (succ e) | inr x | m , k = mkd m e

mkdrefl : ∀ n e n' e'
  → n ≡ n'
  → e ≡ e'
  -------------------------------
  → mkd n e ≡ mkd n' e'
mkdrefl n e .n .e refl refl = refl

mkdzero : (e : ℕ) → mkd 0 e ≡ mkd 0 0
mkdzero zero = refl
mkdzero (succ e) with (odd 0)??
mkdzero (succ e) | inl ()
mkdzero (succ e) | inr x with (iszero e)??
mkdzero (succ zero) | inr x | inl x₁ = drefl
mkdzero (succ (succ e)) | inr x | inl ()
mkdzero (succ zero) | inr x | inr ()
mkdzero (succ (succ e)) | inr x | inr x₁ = mkdzero e

mkd-sound : (n e : ℕ) → num$ (mkd n e) * exp2 e ≡ n * exp2 (pow$ (mkd n e))
mkd-sound n zero = refl
mkd-sound n (succ e) with (odd n)??
mkd-sound n (succ e) | inl x = refl
mkd-sound n (succ e) | inr x with (not-odd-form n x)
mkd-sound n (succ e) | inr x | m , y rewrite
  y
  | *distr (num$ (mkd m e)) (exp2 e) (exp2 e)
  | *distr-r m m (exp2 (pow$ (mkd m e)))
  | mkd-sound m e
  = refl

mkd-norm : ∀ n e → (x : normalized n e ≡ true) →
  dyadic n e x ≡ mkd n e
mkd-norm n zero x = drefl
mkd-norm n (succ e) x with (odd n)??
mkd-norm n (succ e) x | inl y = drefl
mkd-norm n (succ e) x | inr y with (not-odd-form n y)
mkd-norm n (succ e) x | inr y | m , k = refute (odd n) x y
  where
    refute : (c : Bool) → or c false ≡ true → c ≡ false → dyadic n (succ e) x ≡ (mkd m e)
    refute .false () refl
    
cross≡ : (n e n' e' : ℕ)
  → n * exp2 e' ≡ n' * exp2 e
  ------------------------------------------------------------------
  → num$ (mkd n  e ) * exp2 (pow$ (mkd n' e')) ≡
    num$ (mkd n' e') * exp2 (pow$ (mkd n  e ))
cross≡ n e n' e' p with (iszero n)??
cross≡ n e n' e' p | inl x rewrite
  (iszero-sound n x)
  | 0≡a*nz n' (exp2 e) (inv p) (exp2-notzero e)
  | mkdzero e
  | mkdzero e'
  = refl
cross≡ n e n' e' p | inr x with (iszero n')??
cross≡ n e n' e' p | inr x | inl y rewrite
  (iszero-sound n' y)
  | 0≡a*nz n (exp2 e') p (exp2-notzero e')
  | mkdzero e
  | mkdzero e'  
  = refl
cross≡ n e n' e' p | inr x | inr y with (mkd-sound n e) | (mkd-sound n' e')
... | w | w' = *bicross
  (num$ (mkd n e))
  (exp2 (pow$ (mkd n e)))
  n (exp2 e) n' (exp2 e')
  (num$ (mkd n' e'))
  (exp2 (pow$ (mkd n' e')))
  x y w p (inv w')

c≡ : {n e n' e' : ℕ}
  → n * exp2 e' ≡ n' * exp2 e
  ------------------------------------------------------------------
  → num$ (mkd n  e ) * exp2 (pow$ (mkd n' e')) ≡
    num$ (mkd n' e') * exp2 (pow$ (mkd n  e ))
c≡ {n} {e} {n'} {e'} = cross≡ n e n' e'

dmk≡ : ∀ n e n' e' → n * exp2 e' ≡ n' * exp2 e → mkd n e ≡ mkd n' e'
dmk≡ n e n' e' p = d≡ (cross≡ n e n' e' p)

-- Some useful constants.
zer : D
zer = mkd 0 0

oned : D
oned = mkd 1 0

twod : D
twod = mkd 2 0

half : D
half = mkd 1 1

-- Addition of dyadic rationals.
_+d_ : D → D → D
(_+d_) (dyadic n e x) (dyadic n' e' x') = mkd (n * exp2 e' + n' * exp2 e) (e + e')

_+d'_ : D → D → D
(_+d'_) a b = mkd (n * exp2 e' + n' * exp2 e) (e + e')
  where
    n = num$ a
    e = pow$ a
    n' = num$ b
    e' = pow$ b

-- Multiplication of dyadic rationals.
_*d_ : D → D → D
(_*d_) (dyadic n e x) (dyadic n' e' x') = mkd (n * n') (e + e')

-- Addition and multiplication in terms of the numerator and the
-- denominator.
add-numden : (a b : D) → (_+d_) a b ≡ mkd (num$ a * exp2 (pow$ b) + num$ b * exp2 (pow$ a)) (pow$ a + pow$ b)
add-numden (dyadic n e x) (dyadic n₁ e₁ x₁) = refl

mult-numden : (a b : D) → (_*d_) a b ≡ mkd (num$ a * num$ b) (pow$ a + pow$ b)
mult-numden (dyadic n e x) (dyadic n₁ e₁ x₁) = refl

mk-const : ∀ n e →
  Σ ℕ (λ k → (iszero k ≡ false) × ((n ≡ k * num$ (mkd n e)) × (exp2 e ≡ k * exp2 (pow$ (mkd n e)))))
mk-const n zero = 1 , (refl , ((inv (+rzero n)) , refl))
mk-const n (succ e) with (odd n)??
mk-const n (succ e) | inl x = 1 , (refl , ((inv (+rzero n)) , (inv (+rzero (exp2 e + exp2 e)))))
mk-const n (succ e) | inr x with (not-odd-form n x)
mk-const n (succ e) | inr x | m , α with (mk-const m e)
mk-const n (succ e) | inr x | m , α | k' , (β1 , (β2 , β3)) = 2 * k' , (lemma1 k' β1 , (lemma2 , lemma3))
  where
    lemma1 : ∀ a → iszero a ≡ false → iszero (a + (a + zero)) ≡ false
    lemma1 zero ()
    lemma1 (succ a) p = refl

    lemma2 : n ≡ (k' + (k' + zero)) * num$ (mkd m e)
    lemma2 rewrite +rzero k'
      | *comm (k' + k') (num$ (mkd m e)) 
      | *distr (num$ (mkd m e)) k' k'
      | *comm (num$ (mkd m e)) k'
      | inv β2
      | α
      = refl

    lemma3 : exp2 e + exp2 e ≡ (k' + (k' + zero)) * exp2 (pow$ (mkd m e))
    lemma3 rewrite +rzero k'
      | *comm (k' + k') (exp2 (pow$ (mkd m e)))
      | *distr (exp2 (pow$ (mkd m e))) k' k'
      | *comm (exp2 (pow$ (mkd m e))) k'
      | inv β3
      = refl

-- Addition of non-normalized fractions.
add-mk : ∀ n e n' e' → (_+d_) (mkd n e) (mkd n' e') ≡ mkd (n * exp2 e' + n' * exp2 e) (e + e')
add-mk n e n' e' with (mk-const n e) | (mk-const n' e')
add-mk n e n' e' | k , (α1 , (α2 , α3)) | k' , (α1' , (α2' , α3')) rewrite
  add-numden (mkd n e) (mkd n' e') =
    dmk≡ (num$ (mkd n e) * exp2 (pow$ (mkd n' e')) +
      num$ (mkd n' e') * exp2 (pow$ (mkd n e))) (pow$ (mkd n e) + pow$ (mkd n' e'))      
      (n * exp2 e' + n' * exp2 e)
      (e + e')
      lemma
      where
        lemma2 : ∀ k k' n e n' e' m f m' f'
          → n ≡ k * m
          → n' ≡ k' * m'
          → exp2 e ≡ k * exp2 f
          → exp2 e' ≡ k' * exp2 f'
          → k' * (k * ((m * exp2 f' + m' * exp2 f) * exp2 (e + e'))) ≡
            k' * (k * ((n * exp2 e' + n' * exp2 e) * exp2 (f + f')))
        lemma2 k k' n e n' e' m f m' f' u v w x
          rewrite
          *assoc k (m * exp2 f' + m' * exp2 f) (exp2 (e + e'))
          | *distr k (m * exp2 f') (m' * exp2 f)
          | *assoc k m (exp2 f')
          | inv u
          | *comm m' (exp2 f)
          | *assoc k (exp2 f) m'
          | inv w
          | *assoc k' (n * exp2 f' + exp2 e * m') (exp2 (e + e'))
          | *distr k' (n * exp2 f') (exp2 e * m')
          | *comm n (exp2 f')
          | *assoc k' (exp2 f') n
          | inv x
          | *comm (exp2 e) m'
          | *assoc k' m' (exp2 e)
          | inv v
          | *comm (exp2 e') n
          | *assoc k (n * exp2 e' + n' * exp2 e) (exp2 (f + f'))
          | *comm k (n * exp2 e' + n' * exp2 e)
          | inv (*assoc (n * exp2 e' + n' * exp2 e) k (exp2 (f + f')))
          | *assoc k' (n * exp2 e' + n' * exp2 e) (k * exp2 (f + f'))
          | *comm k' (n * exp2 e' + n' * exp2 e)
          | inv (*assoc (n * exp2 e' + n' * exp2 e) k' (k * exp2 (f + f')))
          | exp2plus f f'
          | *assoc k (exp2 f) (exp2 f')
          | inv w
          | *comm (exp2 e) (exp2 f')
          | *assoc k' (exp2 f') (exp2 e)
          | inv x
          | inv (exp2plus e' e)
          | +comm e' e
          = refl

        lemma : (num$ (mkd n e) * exp2 (pow$ (mkd n' e')) +
          num$ (mkd n' e') * exp2 (pow$ (mkd n e))) * exp2 (e + e') ≡
          (n * exp2 e' + n' * exp2 e) * exp2 (pow$ (mkd n e) + pow$ (mkd n' e'))
        lemma = *inj k _ _ α1 (*inj k' _ _ α1'
          (lemma2 k k' n e n' e' _ (pow$ (mkd n e)) _ (pow$ (mkd n' e')) α2 α2' α3 α3'))
          
-- Multiplication of non-normalized fractions.
mult-mk : ∀ n e n' e' → (_*d_) (mkd n e) (mkd n' e') ≡ mkd (n * n') (e + e')
mult-mk n e n' e' with (mk-const n e) | (mk-const n' e')
mult-mk n e n' e' | k , (α1 , (α2 , α3)) | k' , (α1' , (α2' , α3')) rewrite
  mult-numden (mkd n e) (mkd n' e')
  = dmk≡ (num$ (mkd n e) * num$ (mkd n' e')) (pow$ (mkd n e) + pow$ (mkd n' e')) (n * n') (e + e')
    (*inj k _ _ α1 (*inj k' _ _ α1' (lemma α2 α2' α3 α3')))
    where
      lemma : n ≡ k * num$ (mkd n e)
            → n' ≡ k' * num$ (mkd n' e')
            → exp2 e ≡ k * exp2 (pow$ (mkd n e))
            → exp2 e' ≡ k' * exp2 (pow$ (mkd n' e'))
            → k' * (k * (num$ (mkd n e) * num$ (mkd n' e') * exp2 (e + e'))) ≡
              k' * (k * (n * n' * exp2 (pow$ (mkd n e) + pow$ (mkd n' e'))))
      lemma u1 u2 u3 u4
        rewrite
        *assoc k (num$ (mkd n e) * num$ (mkd n' e')) (exp2 (e + e'))
        | *assoc k (num$ (mkd n e)) (num$ (mkd n' e'))
        | inv u1
        | *comm n (num$ (mkd n' e'))
        | inv (*assoc (num$ (mkd n' e')) n (exp2 (e + e')))
        | *assoc k' (num$ (mkd n' e')) (n * exp2 (e + e'))
        | inv u2
        | *assoc k (n * n') (exp2 (pow$ (mkd n e) + pow$ (mkd n' e')))
        | *comm k (n * n')
        | inv (*assoc (n * n') k (exp2 (pow$ (mkd n e) + pow$ (mkd n' e'))))
        | *assoc k' (n * n') (k * exp2 (pow$ (mkd n e) + pow$ (mkd n' e')))
        | *comm k' (n * n')
        | inv (*assoc (n * n') k' (k * exp2 (pow$ (mkd n e) + pow$ (mkd n' e'))))
        | exp2plus (pow$ (mkd n e)) (pow$ (mkd n' e'))
        | *assoc k (exp2 (pow$ (mkd n e))) (exp2 (pow$ (mkd n' e')))
        | inv u3
        | *assoc k' (exp2 e) (exp2 (pow$ (mkd n' e')))
        | *comm k' (exp2 e)
        | inv (*assoc (exp2 e) k' (exp2 (pow$ (mkd n' e'))))
        | inv u4
        | exp2plus e e'
        | *assoc n' n (exp2 e * exp2 e')
        | *comm n' n
        = refl
        
add-comm : ∀ a b → (_+d_) a b ≡ b +d a
add-comm (dyadic n e x) (dyadic n₁ e₁ x₁) = d≡ (cross≡ _ (e + e₁) _ (e₁ + e) lemma)
  where
    lemma : (n * exp2 e₁ + n₁ * exp2 e) * exp2 (e₁ + e) ≡ (n₁ * exp2 e + n * exp2 e₁) * exp2 (e + e₁)
    lemma rewrite
      +comm e₁ e
      | +comm (n₁ * exp2 e) (n * exp2 e₁)
      = refl

mult-comm : ∀ a b → (_*d_) a b ≡ (_*d_) b a
mult-comm (dyadic n e x) (dyadic n₁ e₁ x₁) = d≡ (cross≡ (n * n₁) (e + e₁) (n₁ * n) (e₁ + e) lemma)
  where
    lemma : n * n₁ * exp2 (e₁ + e) ≡ n₁ * n * exp2 (e + e₁)
    lemma rewrite
      *comm n n₁
      | +comm e e₁
      = refl

-- Lemmas on addition
add-zero : ∀ a → (_+d_) zer a ≡ a
add-zero (dyadic n e x) rewrite mkd-norm n e x | *runit n = d≡ refl

addhalfhalf : (_+d_) half half ≡ oned
addhalfhalf = d≡ refl

-- Lemmas on multiplication
mult-zero : ∀ a → (_*d_) zer a ≡ zer
mult-zero (dyadic n e x) = d≡ (cross≡ zero e zero zero refl)

mult-one : ∀ a → (_*d_) oned a ≡ a
mult-one (dyadic n e x) rewrite +rzero n = inv (mkd-norm n e x)

-- Addition is associative.
add-assoc : ∀ a b c → (_+d_) a ((_+d_) b c) ≡ (_+d_) ((_+d_) a b) c
add-assoc (dyadic n e x) (dyadic n' e' _) (dyadic n'' e'' x'')
  rewrite
    mkd-norm n e x
    | add-mk n e (n' * exp2 e'' + n'' * exp2 e') (e' + e'')
    | mkd-norm n'' e'' x''
    | add-mk (n * exp2 e' + n' * exp2 e) (e + e') n'' e''
    = d≡ (cross≡
       (n * exp2 (e' + e'') + (n' * exp2 e'' + n'' * exp2 e') * exp2 e) (e + (e' + e''))
       ((n * exp2 e' + n' * exp2 e) * exp2 e'' + n'' * exp2 (e + e')) (e + e' + e'')
       lemma)
     where
         lemma : (n * exp2 (e' + e'') + (n' * exp2 e'' + n'' * exp2 e') * exp2 e) * exp2 (e + e' + e'')
                  ≡ ((n * exp2 e' + n' * exp2 e) * exp2 e'' + n'' * exp2 (e + e')) * exp2 (e + (e' + e''))
         lemma rewrite
           +assoc e e' e''
           | *comm (n' * exp2 e'' + n'' * exp2 e') (exp2 e)
           | *distr (exp2 e) (n' * exp2 e'') (n'' * exp2 e')
           | *comm (n * exp2 e' + n' * exp2 e)  (exp2 e'')
           | *distr (exp2 e'') (n * exp2 e') (n' * exp2 e)
           | exp2plus e' e''
           | *assoc (exp2 e'') n (exp2 e')
           | *comm (exp2 e'') n
           | *assoc n (exp2 e') (exp2 e'')
           | *assoc (exp2 e'') n' (exp2 e)
           | *comm (exp2 e'') n'
           | *assoc (exp2 e) n'' (exp2 e')
           | *assoc (exp2 e) n' (exp2 e'')
           | *comm (exp2 e) n'
           | exp2plus e e'
           | *assoc n'' (exp2 e) (exp2 e')
           | *comm n'' (exp2 e)
           | inv (*assoc n (exp2 e'') (exp2 e'))
           | *comm (exp2 e'') (exp2 e')
           | *assoc n (exp2 e') (exp2 e'')
           | +assoc (n * exp2 e' * exp2 e'') (n' * exp2 e * exp2 e'') (exp2 e * n'' * exp2 e')
           | inv (*assoc n' (exp2 e) (exp2 e''))
           | *comm (exp2 e) (exp2 e'')
           | *assoc n' (exp2 e'') (exp2 e)
           = refl

-- Multiplication is associative.
mult-assoc : ∀ a b c → (_*d_) a ((_*d_) b c) ≡ (_*d_) ((_*d_) a b) c
mult-assoc (dyadic n e x) (dyadic n₁ e₁ x₁) (dyadic n₂ e₂ x₂)
  rewrite
    mkd-norm n e x
    | mult-mk n e (n₁ * n₂) (e₁ + e₂)
    | mkd-norm n₂ e₂ x₂
    | mult-mk (n * n₁) (e + e₁) n₂ e₂
    = d≡ (cross≡ (n * (n₁ * n₂)) (e + (e₁ + e₂)) (n * n₁ * n₂) (e + e₁ + e₂) lemma)
    where
      lemma : n * (n₁ * n₂) * exp2 (e + e₁ + e₂) ≡ n * n₁ * n₂ * exp2 (e + (e₁ + e₂))
      lemma rewrite
        *assoc n n₁ n₂
        | +assoc e e₁ e₂
        = refl

-- Addition and multiplication are distributive.
mp-distr : ∀ a b c → (_*d_) a ((_+d_) b c) ≡ (_+d_) ((_*d_) a b) ((_*d_) a c)
mp-distr (dyadic n e x) (dyadic n₁ e₁ x₁) (dyadic n₂ e₂ x₂)
  rewrite
  mkd-norm n e x
  | mult-mk n e (n₁ * exp2 e₂ + n₂ * exp2 e₁) (e₁ + e₂)
  | add-mk (n * n₁) (e + e₁) (n * n₂) (e + e₂)
  = d≡ (cross≡
      (n * (n₁ * exp2 e₂ + n₂ * exp2 e₁)) (e + (e₁ + e₂))
      (n * n₁ * exp2 (e + e₂) + n * n₂ * exp2 (e + e₁)) (e + e₁ + (e + e₂))
      lemma
    )
    where
      lemma :
        n * (n₁ * exp2 e₂ + n₂ * exp2 e₁) * exp2 (e + e₁ + (e + e₂)) ≡
        (n * n₁ * exp2 (e + e₂) + n * n₂ * exp2 (e + e₁)) * exp2 (e + (e₁ + e₂))
      lemma rewrite
        inv (+assoc e e₁ (e + e₂))
        | exp2plus e (e₁ + (e + e₂))
        | *distr n (n₁ * exp2 e₂) (n₂ * exp2 e₁)
        | *assoc (n * (n₁ * exp2 e₂) + n * (n₂ * exp2 e₁)) (exp2 e) (exp2 (e₁ + (e + e₂)))
        | *comm (n * (n₁ * exp2 e₂) + n * (n₂ * exp2 e₁)) (exp2 e)
        | *distr (exp2 e) (n * (n₁ * exp2 e₂)) (n * (n₂ * exp2 e₁))
        | *assoc n n₁ (exp2 e₂)
        | *assoc n n₂ (exp2 e₁)
        | *assoc (exp2 e) (n * n₁) (exp2 e₂)
        | *assoc (exp2 e) (n * n₂) (exp2 e₁)
        | *comm (exp2 e) (n * n₁)
        | *comm (exp2 e) (n * n₂)
        | inv (*assoc (n * n₁) (exp2 e) (exp2 e₂))
        | inv (*assoc (n * n₂) (exp2 e) (exp2 e₁))        
        | inv (exp2plus e e₂)
        | inv (exp2plus e e₁)
        | +assoc e₁ e e₂
        | +comm e₁ e
        | +assoc e e₁ e₂
        = refl

-- Decidable equality
dec≡ : (a b : D) → (a ≡ b) ⊎ ¬ (a ≡ b)
dec≡ (dyadic n e x) (dyadic n₁ e₁ x₁) with ndec≡ n n₁
dec≡ (dyadic n e x) (dyadic n₁ e₁ x₁) | inl refl with ndec≡ e e₁
dec≡ (dyadic n e x) (dyadic .n e₁ x₁) | inl refl | inl refl = inl drefl
dec≡ (dyadic n e x) (dyadic .n e₁ x₁) | inl refl | inr x₂ = inr λ x₃ → x₂ (ap pow$ x₃)
dec≡ (dyadic n e x) (dyadic n₁ e₁ x₁) | inr x₂ = inr λ x₃ → x₂ (ap num$ x₃)







-- Ordering
lt' : D → D → Bool
lt' a b = n * (exp2 e') < n' * (exp2 e)
  where
    n = num$ a
    e = pow$ a
    n' = num$ b
    e' = pow$ b

_<d_ : D → D → Bool
_<d_ (dyadic n e x) (dyadic n' e' x') = n * (exp2 e') < n' * (exp2 e)

lt$ : ∀ a b → a <d b ≡ (num$ a) * (exp2 (pow$ b)) < (num$ b) * (exp2 (pow$ a))
lt$ (dyadic n e x) (dyadic n₁ e₁ x₁) = refl

lthalf : zer <d half ≡ true
lthalf = refl

ltzero : (a : D) → zer <d a ≡ false → a ≡ zer
ltzero (dyadic n e x) p rewrite *runit n | <zero n p = d≡ refl

ltone : zer <d oned ≡ true
ltone = refl

ltzeroref : (a : D) → ¬ (a <d zer ≡ true)
ltzeroref (dyadic n e x) = λ y → true≢false (inv y)

mustbezero : (a : D) → zer <d a ≡ false → a ≡ zer
mustbezero (dyadic n e x) p rewrite *runit n | zero<false n p = lemma e x
  where
    lemma : ∀ e x → dyadic 0 e x ≡ dyadic 0 0 refl
    lemma e x rewrite mkd-norm 0 e x | mkdzero e = refl

infixl 30 _+d_
infixl 35 _*d_
infix 6 _<d_
