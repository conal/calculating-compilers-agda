{-# OPTIONS --type-in-type --rewriting #-}

-- {-# OPTIONS --injective-type-constructors #-}

module Classes where

open import Data.Product renaming (swap to pswap)
open import Data.Unit
open import Function
open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open PE.≡-Reasoning
open import Agda.Builtin.Equality.Rewrite

private
  variable
   A B C D U V Z : Set
   _→k_ : Set → Set → Set

record Category (_→k_ : Set → Set → Set) : Set where
  infixr 5 _∘c_
  field
    idc   : A →k A
    _∘c_  : (B →k C) → (A →k B) → (A →k C)
    .id-l  : ∀ {f : A →k B} → idc ∘c f ≡ f
    .id-r  : ∀ {f : A →k B} → f ∘c idc ≡ f
    .assoc : ∀ {h : C →k D} {g : B →k C} {f : A →k B}
           → (h ∘c g) ∘c f ≡ h ∘c (g ∘c f)
open Category ⦃ … ⦄ public

instance
  _ : Category (λ (A B : Set) → A → B)
  _ = record {
    idc = id ;
    _∘c_ = _∘′_ ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }
