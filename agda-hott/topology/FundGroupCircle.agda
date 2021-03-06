{-# OPTIONS --without-K #-}


-- Agda-hott library.
-- Author: Mario Román

-- Fundamental Group of the Circle.  Follows the proof on the Homotopy
-- Type Theory Book. Encodes ℤ inside the equalities of the circle
-- type and extracts the homotopical structure of equalities using the
-- Univalence Axiom.

open import Base
open import Equality
open import EquationalReasoning
open import numbers.Integers
open import equivalence.Equivalence
open import equivalence.EquivalenceComposition
open import equivalence.Quasiinverses
open import logic.Quotients
open import algebra.Groups
open import algebra.IntegerAction
open import topology.Circle
open import topology.FundamentalGroup
open import equality.Univalence
open import equality.FunctionExtensionality

module topology.FundGroupCircle where

  -- Winds a loop n times on the circle.
  loops : ℤ → Ω S¹ base
  loops n = z-act (Ω-st S¹ base) n loop

  -- Uses univalence to unwind a path over the integers.
  code : S¹ → Type0
  code = S¹-ind Type0 ℤ (ua zequiv-succ)

  tcode-succ : (n : ℤ) → transport code loop n == zsucc n
  tcode-succ n = 
    begin
      transport code loop n ==⟨ refl _ ⟩
      transport ((λ a → a) ∘ code) loop n ==⟨ transport-family loop n ⟩      
      transport (λ a → a) (ap code loop) n ==⟨ ap (λ u → transport (λ a → a) u n) (S¹-βind _ ℤ (ua zequiv-succ)) ⟩
      transport (λ a → a) (ua zequiv-succ) n ==⟨ ap (λ e → (lemap e) n) (ua-β zequiv-succ) ⟩
      zsucc n
    ∎

  tcode-pred : (n : ℤ) → transport code (inv loop) n == zpred n
  tcode-pred n = 
    begin
      transport code (inv loop) n
        ==⟨ refl _ ⟩
      transport ((λ a → a) ∘ code) (inv loop) n
        ==⟨ transport-family (inv loop) n ⟩
      transport (λ a → a) (ap code (inv loop)) n
        ==⟨ ap (λ u → transport (λ a → a) u n) (ap-inv code loop) ⟩
      transport (λ a → a) (inv (ap code loop)) n
        ==⟨ ap (λ u → transport (λ a → a) (inv u) n) (S¹-βind _ ℤ (ua zequiv-succ)) ⟩
      transport (λ a → a) (inv (ua zequiv-succ)) n
        ==⟨ ap (λ u → transport (λ a → a) u n) (inv (ua-inv zequiv-succ)) ⟩      
      transport (λ a → a) (ua (invEqv zequiv-succ)) n
        ==⟨ ap (λ e → (lemap e) n) ((ua-β (invEqv zequiv-succ))) ⟩
      zpred n
    ∎

  encode : (x : S¹) → (base == x) → code x
  encode x p = transport code p zer

  decode : (x : S¹) → code x → (base == x)
  decode = S¹-rec (λ x → (code x → (base == x))) loops (
    begin
      transport (λ x → code x → base == x) loop loops
        ==⟨ transport-fun loop loops ⟩
      transport (λ x → base == x) loop ∘ (loops ∘ transport code (inv loop))
        ==⟨ ap (λ u → u ∘ (loops ∘ transport code (inv loop))) (funext λ p → transport-concat-r loop p) ⟩
      (_· loop) ∘ (loops ∘ transport code (inv loop))
        ==⟨ ap (λ u → (_· loop) ∘ (loops ∘ u)) (funext tcode-pred) ⟩
      (_· loop) ∘ (loops ∘ zpred)
        ==⟨ funext lemma ⟩
      loops
    ∎)
    where
      lemma : (n : ℤ) → ((_· loop) ∘ (loops ∘ zpred)) n == loops n
      lemma zer     = ·-linv loop
      lemma (pos zero) = refl _
      lemma (pos (succ x)) = refl _
      lemma (neg zero) =
        ·-assoc (inv loop) (inv loop) loop ·
        ap (inv loop ·_) (·-linv loop) ·
        inv (·-runit (inv _))
      lemma (neg (succ x)) =
        ·-assoc (loops (neg x) · inv loop) _ loop ·
        ap ((loops (neg x) · (inv loop)) ·_) (·-linv loop) ·
        inv (·-runit _) 

  decode-encode : (x : S¹) → (p : base == x) → decode x (encode x p) == p
  decode-encode .base (refl .base) = refl (refl base)

  encode-decode : (x : S¹) → (c : code x) → encode x (decode x c) == c
  encode-decode x = S¹-rec
      ((λ y → (c : code y) → encode y (decode y c) == c))
      lemma (funext λ _ → z-isSet _ _ _ _) x
    where
      lemma : (n : ℤ) → encode base (loops n) == n
      lemma zer = refl zer
      lemma (pos 0) = tcode-succ zer
      lemma (pos (succ n)) =
        inv (transport-comp-h (loops (pos n)) loop zer) ·
        ap (transport code loop) (lemma (pos n)) ·
        tcode-succ _
      lemma (neg zero) = tcode-pred zer
      lemma (neg (succ n)) =
        inv (transport-comp-h (loops (neg n)) (inv loop) zer) ·
        ap (transport code (inv loop)) (lemma (neg n)) ·
        tcode-pred _

  -- Creates an equivalence between paths and encodings.
  equiv-family : (x : S¹) → (base == x) ≃ code x
  equiv-family x = qinv-≃ (encode x) (decode x , (encode-decode x , decode-encode x))


  -- The fundamental group of the circle is the integers.  In this
  -- proof, univalence is crucial. The next lemma will prove that the
  -- equivalence in fact preserves the group structure.
  fundamental-group-of-the-circle : Ω S¹ base ≃ ℤ
  fundamental-group-of-the-circle = equiv-family base

  preserves-composition : ∀ n m → loops (n +ᶻ m) == loops n · loops m
  preserves-composition n m = z-act+ (Ω-st S¹ base) n m loop

  preserves-inverses : ∀ n → loops (- n) == inv (loops n)
  preserves-inverses n = z-actm (Ω-st S¹ base) n loop
