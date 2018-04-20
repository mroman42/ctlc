module PositiveOrderedField where

record PositiveOrderedField : Set₁ where
  field
    F : Set
    _+_ : F → F → F
    _*_ : F → F → F
    
