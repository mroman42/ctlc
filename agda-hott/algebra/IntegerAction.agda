{-# OPTIONS --without-K  #-}


-- Agda-hott library.
-- Author: Mario Román

-- IntegerAction.  Integers can act on groups. This corresponds to the
-- fact that the integers are the free group on one generator.

open import Base
open import Equality
open import EquationalReasoning
open import numbers.Integers
open import algebra.Groups

module algebra.IntegerAction {ℓ} {M : Type ℓ} (grpst : GroupStructure M) where
  open GroupStructure grpst

  -- Integers acting on a group structure M.
  z-act : ℤ → M → M
  z-act zer            m = e
  z-act (pos zero)     m = m
  z-act (pos (succ x)) m = (z-act (pos x) m) * m
  z-act (neg zero)     m = ginv m
  z-act (neg (succ x)) m = (z-act (neg x) m) * ginv m


  -- Lemmas on how integers act on a group.
  zsucc-act : ∀ n a → z-act (zsucc n) a == (z-act n a * a)
  zsucc-act zer a = inv (lunit a)
  zsucc-act (pos x) a = refl _
  zsucc-act (neg zero) a = inv (grinv a)
  zsucc-act (neg (succ n)) a =
    begin
      z-act (neg n) a                   ==⟨ inv (runit (z-act (neg n) a)) ⟩
      z-act (neg n) a * e               ==⟨ ap (λ section → _*_ (z-act (neg n) a) section) (inv (grinv a)) ⟩
      z-act (neg n) a * (ginv a * a)    ==⟨ assoc (z-act (neg n) a) (ginv a) a ⟩      
      ((z-act (neg n) a * ginv a) * a)
    ∎

  zpred-act : ∀ n a → z-act (zpred n) a == (z-act n a * ginv a)
  zpred-act zer a = inv (lunit (ginv a))
  zpred-act (pos zero) a = inv (glinv a)
  zpred-act (pos (succ x)) a = 
    begin
      z-act (zpred (pos (succ x))) a   ==⟨ refl _ ⟩
      z-act (pos x) a                  ==⟨ inv (runit _) ⟩
      z-act (pos x) a * e              ==⟨ ap (λ section → _*_ (z-act (pos x) a) section) (inv (glinv a)) ⟩
      z-act (pos x) a * (a * ginv a)   ==⟨ assoc (z-act (pos x) a) a (ginv a) ⟩
      (z-act (pos x) a * a) * ginv a   ==⟨ refl _ ⟩      
      z-act (pos (succ x)) a * ginv a
    ∎
  zpred-act (neg x) a = refl _
    

  act-zsucc : ∀ n a → z-act (zsucc n) a == (a * z-act n a)
  act-zsucc zer a = inv (runit a)
  act-zsucc (pos zero) a = refl _
  act-zsucc (pos (succ x)) a = 
    begin
       ((z-act (pos x) a * a) * a) ==⟨ ap (λ u → u * a) (act-zsucc (pos x) a) ⟩
       ((a * z-act (pos x) a) * a) ==⟨ inv (assoc a (z-act (pos x) a) a) ⟩       
       (a * (z-act (pos x) a * a))
    ∎
  act-zsucc (neg zero) a = inv (glinv a)
  act-zsucc (neg (succ x)) a =
    begin
       z-act (neg x) a                    ==⟨ inv (runit (z-act (neg x) a)) ⟩
       (z-act (neg x) a) * e              ==⟨ ap (λ section → _*_ (z-act (neg x) a) section) (inv (glinv a)) ⟩
       (z-act (neg x) a) * (a * ginv a)   ==⟨ assoc (z-act (neg x) a) a (ginv a) ⟩
       ((z-act (neg x) a) * a) * ginv a   ==⟨ ap (λ s → s * (ginv a)) (inv (zsucc-act (neg x) a)) ⟩       
       (z-act (zsucc (neg x)) a) * ginv a ==⟨ ap (λ s → s * (ginv a)) (act-zsucc (neg x) a) ⟩       
       (a * (z-act (neg x) a)) * ginv a   ==⟨ inv (assoc a (z-act (neg x) a) (ginv a)) ⟩
       (a * (z-act (neg x) a * ginv a))
    ∎

  act-zpred : ∀ n a → z-act (zpred n) a == (ginv a * z-act n a)
  act-zpred n a = 
    begin
      z-act (zpred n) a  ==⟨ inv (lunit (z-act (zpred n) a)) ⟩
      e * z-act (zpred n) a  ==⟨ ap (λ section → _*_ section (z-act (zpred n) a)) (inv (grinv a)) ⟩
      (ginv a * a) * z-act (zpred n) a  ==⟨ inv (assoc _ a _) ⟩
      ginv a * (a * z-act (zpred n) a)  ==⟨ ap (λ section → _*_ (ginv a) section) (inv (act-zsucc (zpred n) a)) ⟩
      ginv a * z-act (zsucc (zpred n)) a ==⟨ ap (λ u → (ginv a * (z-act u a))) (zsuccpred-id n) ⟩
      ginv a * z-act n a
    ∎

  z-act+ : ∀ n m a → z-act (n +ᶻ m) a == (z-act n a * z-act m a)
  z-act+ zer m a = inv (lunit (z-act m a))
  z-act+ (pos zero) m a = act-zsucc m a
  z-act+ (pos (succ x)) m a = 
    begin
      z-act (zsucc (pos x +ᶻ m)) a        ==⟨ act-zsucc (pos x +ᶻ m) a ⟩
      a * z-act (pos x +ᶻ m) a            ==⟨ ap (λ s → a * s) (z-act+ (pos x) m a) ⟩
      a * (z-act (pos x) a * z-act m a)   ==⟨ assoc a (z-act (pos x) a) (z-act m a) ⟩
      (a * z-act (pos x) a) * z-act m a   ==⟨ ap (_* z-act m a) (inv (act-zsucc (pos x) a)) ⟩
      (z-act (pos (succ x)) a) * z-act m a
    ∎
  z-act+ (neg zero) m a = act-zpred m a
  z-act+ (neg (succ x)) m a =
    begin
      z-act (zpred (neg x +ᶻ m)) a             ==⟨ act-zpred (neg x +ᶻ m) a ⟩
      ginv a * z-act (neg x +ᶻ m) a            ==⟨ ap (λ section → _*_ (ginv a) section) (z-act+ (neg x) m a) ⟩
      ginv a * (z-act (neg x) a * z-act m a)  ==⟨ assoc (ginv a) (z-act (neg x) a) (z-act m a) ⟩
      (ginv a * z-act (neg x) a) * z-act m a  ==⟨ inv (ap (λ s → s * (z-act m a)) (act-zpred (neg x) a)) ⟩
      z-act (neg (succ x)) a * z-act m a
    ∎

  z-actm : ∀ n a → z-act (- n) a == ginv (z-act n a)
  z-actm n a =
    begin
      z-act (- n) a ==⟨ inv (runit (z-act (- n) a)) ⟩
      z-act (- n) a * e ==⟨ ap (z-act (- n) a *_) (inv (glinv (z-act n a))) ⟩
      z-act (- n) a * ((z-act n a) * ginv (z-act n a)) ==⟨ assoc (z-act (- n) a) (z-act n a) _ ⟩
      (z-act (- n) a * (z-act n a)) * ginv (z-act n a) ==⟨ ap (_* ginv (z-act n a)) (inv (z-act+ (- n) n a)) ⟩
      z-act ((- n) +ᶻ n) a * ginv (z-act n a) ==⟨ ap (λ u → z-act u a * ginv (z-act n a)) (+ᶻ-comm (- n) n) ⟩      
      z-act (n +ᶻ (- n)) a * ginv (z-act n a) ==⟨ ap (λ u → z-act u a * ginv (z-act n a)) (+-minus n) ⟩      
      z-act zer a * ginv (z-act n a) ==⟨ refl _ ⟩
      e * ginv (z-act n a) ==⟨ lunit (ginv (z-act n a)) ⟩            
      ginv (z-act n a)
    ∎
