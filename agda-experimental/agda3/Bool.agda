{-# OPTIONS --rewriting #-}

open import Prop
open import Equality
open import Base

module Bool where

  data Bool : Set where
    tt : Bool
    ff : Bool

  [_] : Bool → Prop
  [ b ] = b ≡≡ tt

  -- Decidable equality
  _?? : (a : Bool) → (a ≡ tt) + (a ≡ ff)
  tt ?? = inl refl
  ff ?? = inr refl

  -- Contradiction
  contr : {a : Bool} → (a ≡ tt) × (a ≡ ff) → ⊥
  contr {.tt} (refl , ())

  -- And
  infixl 60 _&_
  _&_ : Bool → Bool → Bool
  tt & b = b
  ff & b = ff

  &tt : ∀ b → b & tt ≡ b
  &tt tt = refl
  &tt ff = refl
  {-# REWRITE &tt #-}

  &ff : ∀ b → b & ff ≡ ff
  &ff tt = refl
  &ff ff = refl
  {-# REWRITE &ff #-}


  -- Or
  infixl 60 _∣_  
  _∣_ : Bool → Bool → Bool
  tt ∣ b = tt
  ff ∣ b = b

  ∣tt : ∀ b → b ∣ tt ≡ tt
  ∣tt tt = refl
  ∣tt ff = refl
  {-# REWRITE ∣tt #-}

  ∣ff : ∀ b → b ∣ ff ≡ b
  ∣ff tt = refl
  ∣ff ff = refl
  {-# REWRITE ∣ff #-}


  -- Not
  ~ : Bool → Bool
  ~ tt = ff
  ~ ff = tt

  ~double : ∀ b → ~ (~ b) ≡ b
  ~double tt = refl
  ~double ff = refl
  {-# REWRITE ~double #-}


  -- Xor
  _⊕_ : Bool → Bool → Bool
  tt ⊕ b = ~ b
  ff ⊕ b = b

  ⊕tt : ∀ b → b ⊕ tt ≡ ~ b
  ⊕tt tt = refl
  ⊕tt ff = refl
  {-# REWRITE ⊕tt #-}

  ⊕ff : ∀ b → b ⊕ ff ≡ b
  ⊕ff tt = refl
  ⊕ff ff = refl
  {-# REWRITE ⊕ff #-}  

  -- Addition in Z2
  infixl 60 _+ᵇ_ 
  _+ᵇ_ : Bool → Bool → Bool
  tt +ᵇ c = c
  ff +ᵇ c = ~ c

  +ᵇtt : ∀ b → b +ᵇ tt ≡ b
  +ᵇtt tt = refl
  +ᵇtt ff = refl
  {-# REWRITE +ᵇtt #-}  

  +ᵇff : ∀ b → b +ᵇ ff ≡ ~ b
  +ᵇff tt = refl
  +ᵇff ff = refl
  {-# REWRITE +ᵇff #-}  

  +ᵇneg : ∀ a b → (~ a) +ᵇ b ≡ ~ (a +ᵇ b)
  +ᵇneg tt b = refl
  +ᵇneg ff b = refl
  {-# REWRITE +ᵇneg #-}

  +ᵇneg-l : ∀ a b → a +ᵇ (~ b) ≡ ~ (a +ᵇ b)
  +ᵇneg-l tt b = refl
  +ᵇneg-l ff b = refl
  {-# REWRITE +ᵇneg-l #-}  

  +ᵇdouble : ∀ a → a +ᵇ a ≡ tt
  +ᵇdouble tt = refl
  +ᵇdouble ff = refl
  {-# REWRITE +ᵇdouble #-}

  +ᵇassoc : ∀ a b c → (a +ᵇ b) +ᵇ c ≡ a +ᵇ (b +ᵇ c)
  +ᵇassoc tt b c = refl
  +ᵇassoc ff b c = refl
  {-# REWRITE +ᵇassoc #-}

  -- Product in Z2
  infixl 60 _*ᵇ_  
  _*ᵇ_ : Bool → Bool → Bool
  tt *ᵇ b = tt
  ff *ᵇ b = b

  *ᵇtt : ∀ b → b *ᵇ tt ≡ tt
  *ᵇtt tt = refl
  *ᵇtt ff = refl
  {-# REWRITE *ᵇtt #-}

  *ᵇff : ∀ b → b *ᵇ ff ≡ b
  *ᵇff tt = refl
  *ᵇff ff = refl
  {-# REWRITE *ᵇff #-}  

  -- Implies
  _=>_ : Bool → Bool → Bool
  a => b = (~ a) ∣ b
