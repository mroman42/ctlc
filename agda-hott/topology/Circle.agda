{-# OPTIONS --without-K #-}


-- Agda-hott library.
-- Author: Mario Román

-- Circle.  The circle type is constructed by postulating a type with
-- a single element (base) and a nontrivial path (loop).

open import Base
open import Equality

module topology.Circle where

  private
    -- A private declaration of the type prevents pattern matching and
    -- allows us to postulate higher-inductive types without losing
    -- consistency.
    
    -- This technique is known as the Dan Licata's trick, and it is
    -- used in the HoTT-Agda library.
    data !S¹ : Type0 where
      !base : !S¹

  S¹ : Type0
  S¹ = !S¹
  
  base : S¹
  base = !base

  -- Nontrivial path on the circle.
  postulate loop : base == base

  -- Recursion principle on points
  S¹-rec : ∀{ℓ} (P : S¹ → Type ℓ) (x : P base) (p : transport P loop x == x) → ((t : S¹) → P t)
  S¹-rec P x p !base = x

  -- Recursion principle on paths
  postulate S¹-βrec : ∀{ℓ} (P : S¹ → Type ℓ) (x : P base) (p : transport P loop x == x)
                      → apd (S¹-rec P x p) loop == p
            
  -- Induction principle on points
  S¹-ind : ∀{ℓ} (A : Type ℓ) (a : A) (p : a == a) → (S¹ → A)
  S¹-ind A a p !base = a

  -- Induction principle on paths
  postulate S¹-βind : ∀{ℓ} (A : Type ℓ) (a : A) (p : a == a)
                      → ap (S¹-ind A a p) loop == p
