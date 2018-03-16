module Metaprogramming.Autoquote where

open import Reflection
open import Data.Unit
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Maybe
-- open import Relation.Nullary.Core using (yes; no)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Vec hiding (map)
open import Metaprogramming.Util.PropEqNat

{-
here we'll try and generalise the concrete Agda term->Term->AST process
idea: provide a table with (Name, Constructor ∈ AST) and
we'll try and quote it.

examples on how to use this module are briefly presented in
Metaprogramming.ExampleAutoquote, but a more detailed real-life
use-case is presented in the bottom half of the module Proofs.TautologyProver.

For even more details, refer to the thesis in this repository.
-}

-- this definition is copied from the standard library, Data.Vec.N-Ary,
-- because given the variable astType we don't want to have
-- to use type-in-type. The thing is, at ConstructorMapping, we use N-ary
-- on an as-yet undefined astType, and Agda isn't able to infer the level (zero)
-- N-ary should have. We side-step this by instantiating N-ary directly.
N-ary : (n : ℕ) → Set → Set → Set
N-ary zero    A B = B
N-ary (suc n) A B = A → N-ary n A B

_$ⁿ_ : ∀ {n} {A : Set} {B : Set} → N-ary n A B → (Vec A n → B)
f $ⁿ []       = f
f $ⁿ (x ∷ xs) = f x $ⁿ xs
-- end copy from stdlib

getArity : Type → ℕ
getArity (var x args) = 0
getArity (con c args) = 0
getArity (def f args) = 0
getArity (lam v t) = 0
getArity (pi t₁ t) = 1 + getArity t
getArity (sort x) = 0
getArity unknown = 0

-- a constructor mapping takes the arity of a constructor (a natural
-- representing how many arguments it takes), it's Name (which is Agda's internal
-- representation and can be retrieved using the quote keyword, i.e. `quote zero`), and
-- the actual constructor, packed in an N-ary function, which will make it easier to apply
-- the arguments retrieved from a List (Arg Term) to the constructor.
data ConstructorMapping (astType : Set) : Set₁ where
  _↦_ : (n : Name) → N-ary (getArity (type n)) astType astType → ConstructorMapping astType

-- here we simply say that a mapping table is a "variable" constructor (assumed to take one
-- natural as argument representing the de Bruijn index of that variable in whatever context
-- it was quoted in), and a list of mappings from names to real constructors.
Table : Set → Set₁
Table a = ((ℕ → a) × List (ConstructorMapping a))
  
-- see if a given concrete name is to be found in a list of constructor mappings.
-- if we manage to find it, return the whole entry.
lookupName : {a : Set} → List (ConstructorMapping a) → Name → Maybe (ConstructorMapping a)
lookupName [] name = nothing
lookupName (x ↦ x₁ ∷ tab) name with name ≟-Name x
lookupName (x ↦ x₁ ∷ tab) name | yes p = just (x ↦ x₁)
lookupName (x ↦ x₁ ∷ tab) name | no ¬p = lookupName tab name

mutual
  -- see if we can find a Name in the constructor table, and if
  -- possible, apply the AST-constructor we find this way to the list
  -- of arguments. this list is made by calling convertArgs on the
  -- list of arguments to that Term.
  handleNameArgs : {a : Set} → Table a → Name → List (Arg Term) → Maybe a
  handleNameArgs (vc , tab) name args with lookupName tab name
  handleNameArgs (vc , tab) name args | just (x ↦ x₁)   with convertArgs (vc , tab) args
  handleNameArgs (vc , tab) name args | just (x₁ ↦ x₂)   | just x with getArity (type x₁) | getArity (type x₁) ≟-Nat length x
  handleNameArgs (vc , tab) name args | just (x₁ ↦ x₂)   | just x | .(length x) | yes = just (x₂ $ⁿ fromList x)
  handleNameArgs (vc , tab) name args | just (x₁ ↦ x₂)   | just x | arity       | no  = nothing
  handleNameArgs (vc , tab) name args | just (x ↦ x₁)   | nothing = nothing
  handleNameArgs (vc , tab) name args | nothing = nothing

  -- convert a list of arguments (such as those applied to variables
  -- and definitions (see the thesis section on Agda's reflection data
  -- types)) to a list of objects of type a, a being the type of the
  -- AST we're trying to quote to.
  convertArgs : {a : Set} → Table a → List (Arg Term) → Maybe (List a)
  convertArgs tab [] = just []
  convertArgs tab (arg v r x ∷ ls) with convert tab x
  convertArgs tab (arg v r x ∷ ls) | just x₁ with convertArgs tab ls
  convertArgs tab (arg v r x ∷ ls) | just x₂ | just x₁ = just (x₂ ∷ x₁)
  convertArgs tab (arg v r x ∷ ls) | just x₁ | nothing = nothing
  convertArgs tab (arg v r x ∷ ls) | nothing = nothing
  
{-
  convert's arguments are:
  * a : type of AST
  * table : a constructor table
  * the term to quote.

  It might return a value of type a, if all the conversion steps succeed.
-}
  convert : {a : Set} → Table a → Term → Maybe a
  convert (vc , tab) (var x args) = just (vc x)
  convert (vc , tab) (con c args) = handleNameArgs (vc , tab) c args
  convert (vc , tab) (def f args) = handleNameArgs (vc , tab) f args
  convert (vc , tab) (lam v t)    = nothing
  convert (vc , tab) (pi t₁ t₂)   = nothing
  convert (vc , tab) (sort x)     = nothing
  convert (vc , tab) unknown      = nothing

-- this is a rather lamely defined predicate which says that the
-- conversion succeeds. In actual fact, it tries the conversion, and
-- if it succeeds, says the conversion will succeed. We use it later
-- on to get rid of the Maybe, using the trick of passing an
-- implicit-inferrable argument as predicate.
convertManages : {a : Set} → Table a → Term → Set
convertManages t term with convert t term
convertManages t term | just x  = ⊤
convertManages t term | nothing = ⊥
  
-- the API function we expose. We ask for a conversion table and a
-- term, and assuming all goes well (the man argument) we produce an
-- a.
doConvert : {a : Set} → (tab : Table a) → (t : Term) → {man : convertManages tab t} → a
doConvert tab t {man} with convert tab t
doConvert tab t {man} | just x = x
doConvert tab t {() } | nothing
