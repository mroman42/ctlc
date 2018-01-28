{-# OPTIONS --without-K #-}

open import Base
open import Equality
open import equivalence.Equivalence

module equality.DependentProduct where

  module FunctionExtensionality {ℓ} {A B : Type ℓ} {f g : A → B} where
    -- Application of an homotopy
    happly : f == g → ((x : A) → f x == g x)
    happly (refl f) x = refl (f x)
  
    -- The axiom of function extensionality postulates that the
    -- application of homotopies is an equivalence.
    postulate axiomFunExt : isEquiv happly
  
    eqFunExt : (f == g) ≃ ((x : A) → f x == g x)
    eqFunExt = happly , axiomFunExt

    -- From this, the usual notion of function extensionality follows.
    funext : ((x : A) → f x == g x) → f == g
    funext = remap eqFunExt

    -- Beta and eta rules for function extensionality
    funext-betarule : (h : ((x : A) → f x == g x)) → happly (funext h) == h
    funext-betarule h = lrmap-inverse eqFunExt

    funext-etarule : (p : f == g) → funext (happly p) == p
    funext-etarule p = rlmap-inverse eqFunExt
  open FunctionExtensionality public

  -- Function extensionality in the transport case
  module FunctionExtensionalityTransport {ℓᵢ ℓⱼ} {X : Type ℓᵢ} {A B : X → Type ℓⱼ} {x y : X} where
    funext-transport : (p : x == y) → (f : A x → B x) → (g : A y → B y) → 
      ((p ✶) f == g) ≃ ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a))
    funext-transport (refl a) f g = eqFunExt
  
    funext-transport-l : (p : x == y) → (f : A x → B x) → (g : A y → B y) → 
      ((p ✶) f == g) → ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a))
    funext-transport-l p f g = lemap (funext-transport p _ _)

    funext-transport-r : (p : x == y) → (f : A x → B x) → (g : A y → B y) → 
      ((a : A(x)) → (p ✶) (f a) == g ((p ✶) a)) → ((p ✶) f == g)
    funext-transport-r p f g = remap (funext-transport p _ _)
  open FunctionExtensionalityTransport public
