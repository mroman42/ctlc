\begin{code}
module Ctlc where
\end{code}

%<*id>
\begin{code}
id : {A : Set} → A → A
id = λ x → x

data Nat : Set where
  S : Nat → Nat

data ⊥ : Set where

¬ : (A : Set) → Set
¬ A = (A → ⊥)

data _+_(A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

notnotlem : {A : Set} → ¬ (¬ (A + ¬ A))
notnotlem f = f (inr (λ a → f (inl a)))
\end{code}
%</id>

