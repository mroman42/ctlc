{-# OPTIONS --without-K #-}

open import Base
open import Equality

-- Function extensionality, two functions are equal if they take equal
-- inputs to equal outputs.
postulate fext : ∀{ℓᵢ ℓⱼ} {A : Type ℓᵢ} {B : Type ℓⱼ}
                 (f g : A → B) (α : (a : A) → f a == g a) → f == g

