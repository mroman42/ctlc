{-# OPTIONS --rewriting #-}

open import base.Prop
open import base.Base

module base.Bool where

  [_] : Bool → Prop
  [ b ] = b ≡≡ true

  -- Decidable equality
  _?? : (a : Bool) → (a ≡ true) ⊎ (a ≡ false)
  true ?? = inl refl
  false ?? = inr refl

  -- Boolean equality
  _≡?_ : (a b : Bool) → Bool
  false ≡? false = true
  false ≡? true = false
  true ≡? false = false
  true ≡? true = true

  from≡? : {a b : Bool} → (a ≡? b) ≡ true → (a ≡ b)
  from≡? {false} {false} p = refl
  from≡? {false} {true} ()
  from≡? {true} {false} ()
  from≡? {true} {true} p = refl

  to≡? : {a b : Bool} → (a ≡ b) → (a ≡? b) ≡ true
  to≡? {false} refl = refl
  to≡? {true} refl = refl

  -- Contradiction
  contr : {a : Bool} → (a ≡ true) × (a ≡ false) → ⊥
  contr {.true} (refl , ())
  
  -- And
  infixl 60 _&_
  _&_ : Bool → Bool → Bool
  true & b = b
  false & b = false

  &true' : ∀ b → (b & true ≡? b) ≡ true
  &true' true = refl
  &true' false = refl
  {-# REWRITE &true' #-}

  &true : ∀ b → (b & true) ≡ b
  &true b = from≡? refl
  {-# REWRITE &true #-}

  &false' : ∀ b → (b & false ≡? false) ≡ true
  &false' true = refl
  &false' false = refl
  {-# REWRITE &false' #-}

  &false : ∀ b → b & false ≡ false
  &false b = from≡? refl
  {-# REWRITE &false #-}


  -- Or
  infixl 60 _∣_  
  _∣_ : Bool → Bool → Bool
  true ∣ b = true
  false ∣ b = b

  ∣true : ∀ b → b ∣ true ≡ true
  ∣true true = refl
  ∣true false = refl
  {-# REWRITE ∣true #-}

  ∣false : ∀ b → b ∣ false ≡ b
  ∣false true = refl
  ∣false false = refl
  {-# REWRITE ∣false #-}


  -- Not
  ~ : Bool → Bool
  ~ true = false
  ~ false = true

  ~double : ∀ b → ~ (~ b) ≡ b
  ~double true = refl
  ~double false = refl
  {-# REWRITE ~double #-}


  -- Xor
  _⊕_ : Bool → Bool → Bool
  true ⊕ b = ~ b
  false ⊕ b = b

  ⊕true : ∀ b → b ⊕ true ≡ ~ b
  ⊕true true = refl
  ⊕true false = refl
  {-# REWRITE ⊕true #-}

  ⊕false : ∀ b → b ⊕ false ≡ b
  ⊕false true = refl
  ⊕false false = refl
  {-# REWRITE ⊕false #-}  

  -- Addition in Z2
  infixl 60 _+ᵇ_ 
  _+ᵇ_ : Bool → Bool → Bool
  true +ᵇ c = c
  false +ᵇ c = ~ c

  +ᵇtrue : ∀ b → b +ᵇ true ≡ b
  +ᵇtrue true = refl
  +ᵇtrue false = refl
  {-# REWRITE +ᵇtrue #-}  

  +ᵇfalse : ∀ b → b +ᵇ false ≡ ~ b
  +ᵇfalse true = refl
  +ᵇfalse false = refl
  {-# REWRITE +ᵇfalse #-}  

  +ᵇneg : ∀ a b → (~ a) +ᵇ b ≡ ~ (a +ᵇ b)
  +ᵇneg true b = refl
  +ᵇneg false b = refl
  {-# REWRITE +ᵇneg #-}

  +ᵇneg-l : ∀ a b → a +ᵇ (~ b) ≡ ~ (a +ᵇ b)
  +ᵇneg-l true b = refl
  +ᵇneg-l false b = refl
  {-# REWRITE +ᵇneg-l #-}  

  +ᵇdouble : ∀ a → a +ᵇ a ≡ true
  +ᵇdouble true = refl
  +ᵇdouble false = refl
  {-# REWRITE +ᵇdouble #-}

  +ᵇassoc : ∀ a b c → (a +ᵇ b) +ᵇ c ≡ a +ᵇ (b +ᵇ c)
  +ᵇassoc true b c = refl
  +ᵇassoc false b c = refl
  {-# REWRITE +ᵇassoc #-}

  -- Product in Z2
  infixl 60 _*ᵇ_  
  _*ᵇ_ : Bool → Bool → Bool
  true *ᵇ b = true
  false *ᵇ b = b

  *ᵇtrue : ∀ b → b *ᵇ true ≡ true
  *ᵇtrue true = refl
  *ᵇtrue false = refl
  {-# REWRITE *ᵇtrue #-}

  *ᵇfalse : ∀ b → b *ᵇ false ≡ b
  *ᵇfalse true = refl
  *ᵇfalse false = refl
  {-# REWRITE *ᵇfalse #-}  

  -- Implies
  _=>_ : Bool → Bool → Bool
  a => b = (~ a) ∣ b
