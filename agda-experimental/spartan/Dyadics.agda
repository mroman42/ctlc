module Dyadics where

open import Naturals


normalized : ℕ → ℕ → Bool
normalized n e = or (odd n) (iszero e)

iszero-normalized : (n e : ℕ) → iszero e ≡ true → normalized n e ≡ true
iszero-normalized n e p rewrite p | or-rtrue (odd n) = refl

odd-normalized : (n e : ℕ) → odd n ≡ true → normalized n e ≡ true
odd-normalized n e p rewrite p = refl

nonzero-normalized : (n e : ℕ) → normalized n (succ e) ≡ true → odd n ≡ true
nonzero-normalized n e p rewrite or-rfalse (odd n) | p = refl

data Dyadic : Set where
  dyadic : (n e : ℕ) → normalized n e ≡ true → Dyadic

numerator : Dyadic → ℕ
numerator (dyadic n _ _) = n

exponent : Dyadic → ℕ
exponent (dyadic _ e _) = e


drefl : ∀ {n} {e} 
  → {p : normalized n e ≡ true}
  → {q : normalized n e ≡ true}
  ------------------------------
  → dyadic n e p ≡ dyadic n e q
drefl {n} {e} {p} {q} rewrite (uip p q) = refl

drefl-app : (n e n' e' : ℕ)
  → n ≡ e
  → n' ≡ e'
  → {p : normalized n e ≡ true}
  → {q : normalized n e ≡ true}
  -------------------------------
  → dyadic n e p ≡ dyadic n e q
drefl-app n e n' e' a b {p} {q} rewrite (uip p q) = refl

drefl' : ∀ a b
  → numerator a * exp2 (exponent b) ≡ numerator b * exp2 (exponent a)
  → a ≡ b
drefl' (dyadic n zero x) (dyadic n' zero x') p rewrite
  *runit n
  | *runit n'
  | p
  = drefl
drefl' (dyadic n zero x) (dyadic n' (succ e') x') p rewrite
  *runit n'
  | inv p
--  | or-rfalse  (odd (n * (exp2 e' + exp2 e'))) 
--  | oddmul n (exp2 e' + exp2 e')
  = {!!}
drefl' (dyadic n (succ e) x) (dyadic n' zero x') p rewrite
  *runit n
  | inv p
  = {!!}
drefl' (dyadic n (succ e) x) (dyadic n' (succ e') x') p
  -- rewrite exp2-even-div n n' (succ e) (succ e') ? ? ?
  = {!exp2-even-div n n' (succ e) (succ e') (nonzero-normalized n e x) (nonzero-normalized n' e' x')!}

mkdyadic : ℕ → ℕ → Dyadic
mkdyadic n zero = dyadic n 0 (or-rtrue (odd n))
mkdyadic n (succ e) with (odd n)??
mkdyadic n (succ e) | inl x = dyadic n (succ e) (odd-normalized n (succ e) x)
mkdyadic n (succ e) | inr x with (not-odd-form n x)
mkdyadic n (succ e) | inr x | m , k = mkdyadic m e

-- mkdyadic : ℕ → ℕ → Dyadic
-- mkdyadic n e with (odd n)??
-- mkdyadic n e | inl x = dyadic n e (ap (λ u → or u (iszero e)) x)
-- mkdyadic n e | inr x with (iszero e)??
-- mkdyadic n e | inr x | inl y = dyadic n e (iszero-normalized n e y) -- (ap (λ u → or (odd n) u) y)
-- mkdyadic n zero | inr x | inr ()
-- mkdyadic n (succ e) | inr x | inr y with (not-odd-form n x)
-- mkdyadic n (succ e) | inr x | inr y | m , _ = mkdyadic m e

mkdrefl : ∀ n e n' e'
  → n ≡ n'
  → e ≡ e'
  -------------------------------
  → mkdyadic n e ≡ mkdyadic n' e'
mkdrefl n e .n .e refl refl = refl

mkdyadiczero : (e : ℕ) → mkdyadic 0 e ≡ mkdyadic 0 0
mkdyadiczero zero = refl
mkdyadiczero (succ e) with (odd 0)??
mkdyadiczero (succ e) | inl ()
mkdyadiczero (succ e) | inr x with (iszero e)??
mkdyadiczero (succ zero) | inr x | inl x₁ = drefl
mkdyadiczero (succ (succ e)) | inr x | inl ()
mkdyadiczero (succ zero) | inr x | inr ()
mkdyadiczero (succ (succ e)) | inr x | inr x₁ = mkdyadiczero e

mkdyadic-sound : (n e : ℕ) → numerator (mkdyadic n e) * exp2 e ≡ n * exp2 (exponent (mkdyadic n e))
mkdyadic-sound n zero = refl
mkdyadic-sound n (succ e) with (odd n)??
mkdyadic-sound n (succ e) | inl x = refl
mkdyadic-sound n (succ e) | inr x with (not-odd-form n x)
mkdyadic-sound n (succ e) | inr x | m , y rewrite
  y
  | *distr (numerator (mkdyadic m e)) (exp2 e) (exp2 e)
  | *distr-r m m (exp2 (exponent (mkdyadic m e)))
  | mkdyadic-sound m e
  = refl

mkdyadic-norm : ∀ n e → (x : normalized n e ≡ true) →
  dyadic n e x ≡ mkdyadic n e
mkdyadic-norm n zero x = drefl
mkdyadic-norm n (succ e) x with (odd n)??
mkdyadic-norm n (succ e) x | inl y = drefl
mkdyadic-norm n (succ e) x | inr y with (not-odd-form n y)
mkdyadic-norm n (succ e) x | inr y | m , k = refute (odd n) x y
  where
    refute : (c : Bool) → or c false ≡ true → c ≡ false → dyadic n (succ e) x ≡ (mkdyadic m e)
    refute .false () refl
    
cross≡ : (n e n' e' : ℕ)
  → n * exp2 e' ≡ n' * exp2 e
  ------------------------------------------------------------------
  → numerator (mkdyadic n  e ) * exp2 (exponent (mkdyadic n' e')) ≡
    numerator (mkdyadic n' e') * exp2 (exponent (mkdyadic n  e ))
cross≡ n e n' e' p with (iszero n)??
cross≡ n e n' e' p | inl x rewrite
  (iszero-sound n x)
  | 0≡a*nz n' (exp2 e) (inv p) (exp2-notzero e)
  | mkdyadiczero e
  | mkdyadiczero e'
  = refl
cross≡ n e n' e' p | inr x with (iszero n')??
cross≡ n e n' e' p | inr x | inl y rewrite
  (iszero-sound n' y)
  | 0≡a*nz n (exp2 e') p (exp2-notzero e')
  | mkdyadiczero e
  | mkdyadiczero e'  
  = refl
cross≡ n e n' e' p | inr x | inr y with (mkdyadic-sound n e) | (mkdyadic-sound n' e')
... | w | w' = *bicross
  (numerator (mkdyadic n e))
  (exp2 (exponent (mkdyadic n e)))
  n (exp2 e) n' (exp2 e')
  (numerator (mkdyadic n' e'))
  (exp2 (exponent (mkdyadic n' e')))
  x y w p (inv w')



-- zer : Dyadic
-- zer = dyadic 0 0 refl

-- add : Dyadic → Dyadic → Dyadic
-- add (dyadic n e x) (dyadic n' e' x') = mkdyadic (n * exp2 e' + n' * exp2 e) (e + e')

-- add-mk : ∀ n e n' e'
--   → add (mkdyadic n e) (mkdyadic n' e') ≡ mkdyadic (n * exp2 e' + n' * exp2 e) (e + e')
-- add-mk n zero n' zero = {!!}
-- add-mk n zero n' (succ e') = {!!}
-- add-mk n (succ e) n' e' = {!!}

-- add-comm : ∀ a b → add a b ≡ add b a
-- add-comm (dyadic n e x) (dyadic n' e' x') rewrite
--   +comm e e' | +comm (n * exp2 e') (n' * exp2 e)
--   = refl
  
-- add-zer-l : ∀ a → add zer a ≡ a
-- add-zer-l (dyadic n e x) rewrite (*runit n) | mkdyadic-norm n e x = refl

-- add-distr : ∀ a b c → add a (add b c) ≡ add (add a b) c
-- add-distr (dyadic n e _) (dyadic n' e' _) (dyadic n'' e'' _) = {!!}
