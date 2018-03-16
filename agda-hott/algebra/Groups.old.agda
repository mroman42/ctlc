{-# OPTIONS --without-K #-}

open import Base
open import Equality
open import EquationalReasoning
open import logic.Sets
open import logic.Quotients
open import numbers.Naturals
open import numbers.Integers
open import equality.DependentProduct

module algebra.Groups {ℓ} where

  record GroupStructure (M : Type ℓ) : Type (lsuc ℓ) where
    constructor group-structure
    field
      -- A group is a monoid
      MisSet : isSet M
      _*_ : M → M → M
      e : M            
      lunit : ∀ x → (e * x) == x
      runit : ∀ x → (x * e) == x
      assoc : ∀ x y z → (x * (y * z)) == ((x * y) * z)

      -- With inverses
      ginv : M → M
      glinv : ∀ g → (g * ginv g) == e
      grinv : ∀ g → (ginv g * g) == e


    module Z-Exponentiation where
      -- Exponentiation in a group.
      -- Some lemmas on exponentiation on a pair of naturals.
      gnn-exp : ℕ × ℕ → M → M
      gnn-exp (zero , zero)   m = e
      gnn-exp (zero , succ b) m = ginv m * gnn-exp (zero , b) m
      gnn-exp (succ a , b)    m = m * gnn-exp (a , b) m
  
      gnn-exp-pred : (m : M) → (a b : ℕ) → gnn-exp (a , succ b) m == (ginv m * gnn-exp (a , b) m)
      gnn-exp-pred m zero     b = refl _
      gnn-exp-pred m (succ a) b = 
        begin
          m * gnn-exp (a , succ b) m          ==⟨ ap (m *_) (gnn-exp-pred m a b) ⟩
          m * (ginv m * gnn-exp (a , b) m)    ==⟨ assoc m (ginv _) _ ⟩
          (m * ginv m) * gnn-exp (a , b) m    ==⟨ ap (_* gnn-exp (a , b) m) (glinv _) ⟩
          e * gnn-exp (a , b) m               ==⟨ ap (_* gnn-exp (a , b) m) (inv (grinv _)) ⟩
          (ginv m * m) * gnn-exp (a , b) m    ==⟨ inv (assoc (ginv m) _ _) ⟩
          ginv m * (m * gnn-exp (a , b) m)
        ∎

      gnn-exp-succ-b : (m : M) → (a b : ℕ) → gnn-exp (a , b) m == gnn-exp (succ a , succ b) m
      gnn-exp-succ-b m zero b = 
        begin
          gnn-exp (zero , b) m                 ==⟨ inv (lunit (gnn-exp (zero , b) m)) ⟩
          e * gnn-exp (zero , b) m             ==⟨ inv (ap (_* (gnn-exp (zero , b) m)) (glinv m)) ⟩
          (m * ginv m) * gnn-exp (zero , b) m  ==⟨ inv (assoc m _ (gnn-exp (zero , b) m)) ⟩
          m * (ginv m * gnn-exp (zero , b) m)
        ∎
      gnn-exp-succ-b m (succ a) b = ap (m *_) (gnn-exp-succ-b m a b)

      gnn-exp-same : (m : M) → (a : ℕ) → gnn-exp (a , a) m == e
      gnn-exp-same m zero     = refl e
      gnn-exp-same m (succ a) = inv (gnn-exp-succ-b m a a) · gnn-exp-same m a
  
      gnn-exp-succ-r : (m : M) → (a b c d : ℕ)
                     → gnn-exp (a , b)      m == gnn-exp (c , d)      m
                     → gnn-exp (succ a , b) m == gnn-exp (succ c , d) m
      gnn-exp-succ-r m a b c d p = ap (m *_) p
  
      gnn-exp-succ-l : (m : M) → (a b c d : ℕ)
                     → gnn-exp (a , b)      m == gnn-exp (c , d)      m
                     → gnn-exp (a , succ b) m == gnn-exp (c , succ d) m
      gnn-exp-succ-l m a b c d p = 
        begin
          gnn-exp (a , succ b) m                ==⟨ inv (lunit (gnn-exp (a , succ b) m)) ⟩
          e * gnn-exp (a , succ b) m            ==⟨ ap (_* (gnn-exp (a , succ b) m)) (inv (grinv m)) ⟩
          (ginv m * m) * gnn-exp (a , succ b) m ==⟨ inv (assoc (ginv m) _ (gnn-exp (a , succ b) m)) ⟩
          ginv m * gnn-exp (succ a , succ b) m  ==⟨ ap (ginv m *_) (inv (gnn-exp-succ-b m a b)) ⟩
          ginv m * gnn-exp (a , b) m            ==⟨ ap (ginv m *_) p ⟩
          ginv m * gnn-exp (c , d) m            ==⟨ ap (ginv m *_) (gnn-exp-succ-b m c d) ⟩
          ginv m * (m * gnn-exp (c , succ d) m) ==⟨ assoc (ginv m) m (gnn-exp (c , succ d) m) ⟩
          (ginv m * m) * gnn-exp (c , succ d) m ==⟨ ap (_* gnn-exp (c , succ d) m) (grinv m) ⟩
          e * gnn-exp (c , succ d) m            ==⟨ lunit (gnn-exp (c , succ d) m) ⟩
          gnn-exp (c , succ d) m
        ∎

      -- gnn-exp-plus : (m : M) → (o a b : ℕ) → gnn-exp (a , b) m == gnn-exp (o +ₙ a , o +ₙ b) m
      -- gnn-exp-plus m zero     a b = refl (gnn-exp (a , b) m)
      -- gnn-exp-plus m (succ o) a b = {!!}
  
      -- gnn-exp-plus-r : (m : M) → (o a b c d : ℕ)
      --                → gnn-exp (a , c) m == gnn-exp (b , d) m
      --                → gnn-exp (o +ₙ a , c) m == gnn-exp (o +ₙ b , d) m
      -- gnn-exp-plus-r m zero     a b c d p = p
      -- gnn-exp-plus-r m (succ o) a b c d p = ap (m *_) (gnn-exp-plus-r m o a b c d p)
    
      gnn-exp-rel : (m : M) → (a b c d : ℕ) → a +ₙ d == c +ₙ b → gnn-exp (a , b) m == gnn-exp (c , d) m
      gnn-exp-rel m zero zero zero zero r = refl (gnn-exp (zero , zero) m)
      gnn-exp-rel m (succ a) zero zero zero ()
      gnn-exp-rel m zero (succ b) zero zero ()
      gnn-exp-rel m (succ a) (succ .(plus a 0)) zero zero (refl .(succ (plus a 0))) =
        ap (λ u → gnn-exp (succ a , succ u) m) (plus-runit a) · gnn-exp-same m (succ a)
      gnn-exp-rel m zero zero (succ c) zero ()
      gnn-exp-rel m (succ a) zero (succ c) zero r =
        gnn-exp-succ-r m a zero c zero (gnn-exp-rel m a zero c zero (succ-inj (plus a zero) (plus c zero) r))
      gnn-exp-rel m zero (succ b) (succ c) zero ()
      gnn-exp-rel m (succ a) (succ b) (succ c) zero r =
        ap (m *_) (gnn-exp-rel m a (succ b) c zero (succ-inj (plus a zero) (plus c (succ b)) r))
      gnn-exp-rel m zero zero zero (succ d) ()
      gnn-exp-rel m (succ a) zero zero (succ d) ()
      gnn-exp-rel m zero (succ b) zero (succ .b) (refl .(succ b)) =
        refl (gnn-exp (zero , succ b) m)
      gnn-exp-rel m (succ a) (succ b) zero (succ d) r =
        gnn-exp-pred m (succ a) b · ap (ginv m *_)
        (gnn-exp-rel m (succ a) b zero d (succ-inj (succ a +ₙ d) (zero +ₙ b)
        (plus-succ (succ a) d · (r · inv (plus-succ zero b)))))
      gnn-exp-rel m zero zero (succ c) (succ .(plus c 0)) (refl .(succ (plus c 0))) = 
        begin
          e                                         ==⟨ inv (gnn-exp-same m (succ c)) ⟩
          gnn-exp (succ c , succ c) m               ==⟨ ap (λ u → gnn-exp (succ c , succ u) m)
                                                        (inv (plus-runit c)) ⟩
          gnn-exp (succ c , succ (plus c zero)) m
        ∎
      gnn-exp-rel m (succ a) zero (succ c) (succ d) r =
        ap (m *_) (gnn-exp-rel _ a _ c _ (succ-inj _ _ r))
      gnn-exp-rel m zero (succ b) (succ c) (succ d) r = 
        begin
          ginv m * gnn-exp (zero , b) m  ==⟨ ap (ginv m *_) (gnn-exp-rel m zero b (succ c) d
                                             (succ-inj d _ (r · inv (plus-succ (succ c) b)))) ⟩
          ginv m * gnn-exp (succ c , d) m ==⟨ inv (gnn-exp-pred m (succ c) d) ⟩
          gnn-exp (succ c , succ d) m
        ∎
      gnn-exp-rel m (succ a) (succ b) (succ c) (succ d) r =
        ap (m *_) (gnn-exp-rel _ a _ c _ (succ-inj _ _ r))

      gz-exp : ℤ → M → M
      gz-exp = QRel-rec gnn-exp welldefined
        where
          welldefined : (u v : ℕ × ℕ) → R {{z-QRel}} u v → gnn-exp u == gnn-exp v
          welldefined (a , b) (c , d) r = funext λ m → gnn-exp-rel m a b c d r
          
    open Z-Exponentiation public

  open GroupStructure {{...}} public

  Group : Type (lsuc ℓ)
  Group = Σ (Type ℓ) GroupStructure
