open import Prop
open import Base

module Booleans where

data Bool : Set where
  true : Bool
  false : Bool

_?? : (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
true ?? = inl refl
false ?? = inr refl


and : Bool → Bool → Bool
and true b = b
and false b = false

and-true : (b : Bool) → and b true ≡ b
and-true true = refl
and-true false = refl

and-false : (b : Bool) → and b false ≡ false
and-false true = refl
and-false false = refl

and-both : (b : Bool) → and b b ≡ b
and-both true = refl
and-both false = refl

not : Bool → Bool
not true = false
not false = true

not-inj : (a b : Bool) → not a ≡ not b → a ≡ b
not-inj true true α = refl
not-inj true false α rewrite α = refl
not-inj false true α rewrite α = refl
not-inj false false α = refl

not-double : (a : Bool) → not (not a) ≡ a
not-double true = refl
not-double false = refl

xor : Bool → Bool → Bool
xor true b = not b
xor false b = b

xor-not-l : (a b : Bool) → xor (not a) b ≡ not (xor a b)
xor-not-l true b rewrite not-double b = refl
xor-not-l false b = refl

xor-not-r : (a b : Bool) → xor a (not b) ≡ not (xor a b)
xor-not-r true b = refl
xor-not-r false b = refl

xor-assoc : (a b c : Bool) → xor a (xor b c) ≡ xor (xor a b) c
xor-assoc true true true = refl
xor-assoc true true false = refl
xor-assoc true false c = refl
xor-assoc false b c = refl

xoraa : ∀ a → xor a a ≡ false
xoraa true = refl
xoraa false = refl

or : Bool → Bool → Bool
or true b = true
or false b = b

or-rtrue : (a : Bool) → or a true ≡ true
or-rtrue true = refl
or-rtrue false = refl

or-rfalse : (a : Bool) → or a false ≡ a
or-rfalse true = refl
or-rfalse false = refl
