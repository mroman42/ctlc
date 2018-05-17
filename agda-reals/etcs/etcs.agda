module etcs.Etcs where

open import Base

-- With prop as subobject classifier, we have a topos (?)

-- Well-pointed -> Function extensionality!

-- Axiom of choice (!)

postulate 
  AC : {X : Set} {Y : X → Set} → ((x : X) → ∥ Y x ∥) → ∥ ((x : X) → Y x) ∥
