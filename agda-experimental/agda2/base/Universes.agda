{-# OPTIONS --without-K #-}


module base.Universes where

  -- Agda universe hierarchy.
  open import Agda.Primitive public

  -- Our Universe hierarchy. It is implemented over the primitive
  -- Agda universe hierarchy but it uses Type instead of Set, the
  -- usual name for the Universe in Agda.  
  Type : (ℓ : Level) → Set (lsuc ℓ)
  Type ℓ = Set ℓ

  -- First levels of the universe hierarchy
  Type0 : Type (lsuc lzero)
  Type0 = Type lzero
    
  Type1 : Type (lsuc (lsuc lzero))
  Type1 = Type (lsuc lzero)
