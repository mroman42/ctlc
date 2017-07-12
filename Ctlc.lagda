\begin{code}
module Ctlc where
\end{code}

%<*false>
\begin{code}
data ⊥ : Set where

¬ : (A : Set) → Set
¬ A = (A → ⊥)
\end{code}
%</false>

%<*nnlem>
\begin{code}
notnotlem : {A : Set} -> ¬ A -> ¬ A
notnotlem = (λ f x → f x)
\end{code}
%</nnlem>
