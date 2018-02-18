{-# OPTIONS --rewriting #-}

open import Equality
open import Base
open import Prop

module naturals.Naturals where

  open import naturals.Definition public renaming
    ( ℕ to ℕ
    ; zero to zeroⁿ
    ; succ to succⁿ
    )
  open import naturals.Successor public renaming
    ( succ-inj-l to succ-inj-lⁿ
    ; succ-inj-r to succ-inj-rⁿ
    ; succ-inj to succ-injⁿ
    )
  open import naturals.Addition public renaming
    ( _+_ to _+ⁿ_
    ; +rzero to +rzeroⁿ
    ; +assoc to +assocⁿ
    ; +comm to +commⁿ
    )
  open import naturals.Ordering public renaming
    ( _<_ to _<ⁿ_
    ; <plus to <plusⁿ
    ; <trans to <transⁿ
    ; ≥zero to ≥zeroⁿ
    )

