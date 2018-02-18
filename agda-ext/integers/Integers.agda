{-# OPTIONS --rewriting #-}

open import Base renaming (_+_ to _+₀_)
open import Equality
open import naturals.Naturals
open import Prop

module integers.Integers where

  open import integers.Definition public renaming
    ( zero to zeroᶻ
    )
  open import integers.Successor public renaming
    ( succ to succᶻ
    )
  open import integers.Addition public renaming
    ( _+_ to _+ᶻ_
    ; - to -ᶻ
    )
  open import integers.Multiplication public renaming
    ( _*_ to _*ᶻ_
    )
  open import integers.Ordering public renaming
    ( _<_ to _<ᶻ_
    )
  open import integers.Even public renaming
    ( div2 to div2ᶻ
    )
