\begin{code}
module Ctlc where
\end{code}

%<*nat>
\begin{code}
  data ℕ : Set where
    zero  : ℕ
    suc   : (n : ℕ) → ℕ
\end{code}
%</nat>

%<*plus>
\begin{code}
  _+_ : ℕ → ℕ → ℕ
  zero   + n = n
  suc m  + n = suc (m + n)
\end{code}
%</plus>
