{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Base
open import Equality
open import EquationalReasoning
open import numbers.Integers
open import equivalence.Equivalence
open import equivalence.EquivalenceComposition
open import equivalence.Quasiinverses
open import logic.Quotients
open import topology.Circle
open import algebra.HigherGroups
open import topology.FundamentalHigherGroup
open import equality.Univalence
open import equality.DependentProduct

module topology.FundGroupCircle where

  loops : ℤ → Ω S¹ base
  loops n = gz-exp {{Ω-st-r S¹ base}} n loop

  code : S¹ → Type1
  code = S¹-ind Type1 ℤ (ua zequiv-succ)

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
  encode x p = transport code p z-zero

  decode : (x : S¹) → code x → (base == x)
  decode = S¹-rec (λ x → (code x → (base == x))) loops (
    begin
      transport (λ x → code x → base == x) loop loops
        ==⟨ {!!} ⟩
      transport (λ x → base == x) loop ∘ (loops ∘ transport code (inv loop))
        ==⟨ {!!} ⟩
      (_· loop) ∘ (loops ∘ transport code (inv loop))
        ==⟨ ap (λ u → (_· loop) ∘ (loops ∘ u)) (funext tcode-pred) ⟩
      (_· loop) ∘ (loops ∘ zpred)
        ==⟨ funext lemma ⟩
      loops
    ∎)
    where
      lemma : (n : ℤ) → ((_· loop) ∘ (loops ∘ zpred)) n == loops n
      lemma n = {!!}
        where
          f : (m : ℕ × ℕ) → ((_· loop) ∘ (loops ∘ zpred)) [ m ] == loops [ m ]
          f (zero , zero) = ·-linv loop
          f (zero , succ b) =
             begin
               ((gz-exp {{Ω-st-r S¹ base}} [(0 , b)] loop · inv loop) · inv loop) · loop
                 ==⟨ ·-assoc (gz-exp {{Ω-st-r S¹ base}} [(0 , b)] loop · inv loop) (inv loop) _ ⟩
               gz-exp {{Ω-st-r S¹ base}} [(0 , b)] loop · inv loop · (inv loop · loop)
                 ==⟨ {!!} ⟩
               gz-exp {{Ω-st-r S¹ base}} [(0 , b)] loop · inv loop · refl _
                 ==⟨ {!!} ⟩
               gz-exp {{Ω-st-r S¹ base}} [(0 , b)] loop · inv loop
             ∎
          f (succ a , b) = {!!}

          -- welldefined : (u v : ℕ × ℕ) → (o : R {{z-QRel}} u v)
          --    → transport (λ u → ((_· loop) ∘ (loops ∘ zpred)) [ u ] == loops [ u ]) (Req o) (f u) == f v
          -- welldefined u v r = ?

  decode-encode : (x : S¹) → (p : base == x) → decode x (encode x p) == p
  decode-encode .base (refl .base) = refl (refl base)

  encode-decode : (x : S¹) → (c : code x) → encode x (decode x c) == c
  encode-decode x = S¹-rec (λ y → (c : code y) → encode y (decode y c) == c) lemma {!!} x
    where
      lemma : (n : ℤ) → encode base (loops n) == n
      lemma = QRel-ind f welldefined
        where
          f : (m : ℕ × ℕ) → encode base (loops [ m ]) == [ m ]
          f (zero , zero)   = refl z-zero
          f (zero , succ b) = 
            begin
              encode base (loops [ zero , succ b ])
                ==⟨ refl _ ⟩
              encode base (loops [ zero , b ] · inv loop)
                ==⟨ refl _ ⟩
              transport code (loops [ zero , b ] · inv loop) z-zero
                ==⟨ inv (transport-comp-h (loops [ zero , b ]) _ _) ⟩
              (transport code (inv loop) ∘ transport code (loops [ zero , b ])) z-zero
                ==⟨ refl _ ⟩
              transport code (inv loop) (transport code (loops [ zero , b ]) z-zero)
                ==⟨ tcode-pred _ ⟩
              zpred (transport code (loops [ zero , b ]) z-zero)
                ==⟨ refl _ ⟩
              zpred (encode base (loops [ zero , b ]))
                ==⟨ ap zpred (f (zero , b)) ⟩
              zpred [ zero , b ]
                ==⟨ refl _ ⟩                
              [ zero , succ b ]
            ∎
          f (succ a , b) = 
            begin
              encode base (loops [ succ a , b ])
                ==⟨ refl _ ⟩
              encode base (loops [ a , b ] · loop)
                ==⟨ refl _ ⟩
              transport code (loops [ a , b ] · loop) z-zero
                ==⟨ inv (transport-comp-h (loops [ a , b ]) loop z-zero) ⟩
              (transport code loop ∘ transport code (loops [ a , b ])) z-zero
                ==⟨ refl _ ⟩
              transport code loop (transport code (loops [ a , b ]) z-zero)
                ==⟨ tcode-succ _ ⟩
              zsucc (transport code (loops [ a , b ]) z-zero)
                ==⟨ refl _ ⟩
              zsucc (encode base (loops [ a , b ]))
                ==⟨ ap zsucc (f (a , b)) ⟩
              zsucc [ a , b ]
                ==⟨ refl _ ⟩ 
              [ succ a , b ]
            ∎

          welldefined : (u v : ℕ × ℕ) → (o : R {{z-QRel}} u v)
                      → transport (λ x → encode base (loops x) == x) (Req o) (f u) == f v
          welldefined u v r = Rtrunc (encode base (loops [ v ])) [ v ] _ _

  equiv-family : (x : S¹) → (base == x) ≃ code x
  equiv-family x = qinv-≃ (encode x) (decode x , (encode-decode x , decode-encode x))

  fundamental-higher-group-of-the-circle : Ω S¹ base ≃ ℤ
  fundamental-higher-group-of-the-circle = equiv-family base

  -- PathtoZ : Ω S¹ base → ℤ
  -- PathtoZ p = transport (λ x → x) (apc p) z-zero
  --   where
  --     apc : base == base → ℤ == ℤ
  --     apc p = ap code p
