{-# OPTIONS --without-K #-}

open import Base
open import numbers.Integers
open import algebra.Groups

module algebra.IntegerAction {ℓ} {M : Type ℓ} (grpst : GroupStructure M) where
  open GroupStructure grpst

  z-act : ℤ → M → M
  z-act zer            m = e
  z-act (pos zero)     m = m
  z-act (pos (succ x)) m = (z-act (pos x) m) * m
  z-act (neg zero)     m = ginv m
  z-act (neg (succ x)) m = (z-act (neg x) m) * ginv m
