\begin{code}
module Ctlc where
\end{code}

%<*id>
\begin{code}
id : {A : Set} → A → A
id a = a
\end{code}
%</id>

%<*nnlem>
\begin{code}
data ⊥ : Set where

¬ : (A : Set) → Set
¬ A = (A → ⊥)

data _+_(A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

notnotlem : {A : Set} → ¬ (¬ (A + ¬ A))
notnotlem f = f (inr (\ a → f (inl a)))
\end{code}
%</nnlem>
