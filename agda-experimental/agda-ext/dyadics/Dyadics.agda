{-# OPTIONS --rewriting #-}

open import Base hiding (_+_)
open import Equality
open import naturals.Naturals
open import integers.Integers 
open import Prop
open import Bool

module dyadics.Dyadics where

  open import dyadics.Definition public renaming
    ( _+_ to _+ᵈ_
    ; _*_ to _*ᵈ_
    ; _<_ to _<ᵈ_
    ; 0,0 to 0,0ᵈ
    ; half to halfᵈ
    )
