module Metaprogramming.Util.PropEqNat where

open import Data.Nat

{-
   Some very boring helpers for equality on Naturals.
-}

data EqN : ℕ → ℕ → Set where
  yes : {m : ℕ}   → EqN m m
  no  : {m n : ℕ} → EqN m n

≟-Nat-cong : (m : ℕ) → (n : ℕ) → EqN m n → EqN (suc m) (suc n)
≟-Nat-cong .n n yes = yes
≟-Nat-cong  m n no  = no

_≟-Nat_ : (m : ℕ) → (n : ℕ) → EqN m n
zero  ≟-Nat zero  = yes
zero  ≟-Nat suc n = no
suc m ≟-Nat zero  = no
suc m ≟-Nat suc n = ≟-Nat-cong m n (m ≟-Nat n)

