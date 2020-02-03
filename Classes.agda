{-# OPTIONS --type-in-type --rewriting #-}

module Classes where

open import Data.Product renaming (swap to pswap)
open import Data.Sum renaming (swap to sswap)
open import Data.Unit
open import Function renaming (_∘_ to _∘→_; id to id→)
open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open PE.≡-Reasoning
open import Agda.Builtin.Equality.Rewrite

private
  variable
   A B C D U V Z : Set
   _↝_ : Set → Set → Set

record Category (_↝_ : Set → Set → Set) : Set where
  infixr 5 _∘_
  field
    id   : A ↝ A
    _∘_  : (B ↝ C) → (A ↝ B) → (A ↝ C)
    .id-l  : ∀ {f : A ↝ B} → id ∘ f ≡ f
    .id-r  : ∀ {f : A ↝ B} → f ∘ id ≡ f
    .assoc : ∀ {h : C ↝ D} {g : B ↝ C} {f : A ↝ B}
           → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
open Category ⦃ … ⦄ public

instance
  →-Category : Category (λ (A B : Set) → A → B)
  →-Category = record {
    id = id→ ;
    _∘_ = _∘′_ ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

record MonoidalP (_↝_ : Set → Set → Set) : Set where
  field
    ⦃ cat ⦄ : Category _↝_
    _⊗_ : (A ↝ C) → (B ↝ D) → ((A × B) ↝ (C × D))
open MonoidalP ⦃ … ⦄ public

instance
  →-MonoidalP : MonoidalP (λ (A B : Set) → A → B)
  →-MonoidalP = record {
    _⊗_ = λ { f g (a , b) → (f a , g b) } }

record Cartesian _↝_ : Set where
  field
    ⦃ _↝_MonoidalP ⦄ : MonoidalP _↝_
    exl : (A × B) ↝ A
    exr : (A × B) ↝ B
    dup : A ↝ (A × A)
open Cartesian ⦃ … ⦄ public

_△_ : ⦃ _ : Cartesian _↝_ ⦄ → (A ↝ C) → (A ↝ D) → (A ↝ (C × D))
f △ g = (f ⊗ g) ∘ dup

instance
  →-Cartesian : Cartesian (λ (A B : Set) → A → B)
  →-Cartesian = record {
    exl = proj₁ ;
    exr = proj₂ ;
    dup = λ a → (a , a) }

record AssociativeCat (_↝_ : Set → Set → Set) : Set where
  field
    rassoc : ((A × B) × C) ↝ (A × (B × C))
    lassoc : (A × (B × C)) ↝ ((A × B) × C)
open AssociativeCat ⦃ … ⦄ public

instance
  →-AssociativeCat : AssociativeCat (λ (A B : Set) → A → B)
  →-AssociativeCat = record {
    rassoc = λ { ((a , b) , c) → a , b , c } ;
    lassoc = λ { (a , b , c) → (a , b) , c } }

record BraidedCat (_↝_ : Set → Set → Set) : Set where
  field
    swap : (A × B) ↝ (B × A)
open BraidedCat ⦃ … ⦄ public

instance
  →-BraidedCat : BraidedCat (λ (A B : Set) → A → B)
  →-BraidedCat = record { swap = λ {(a , b) → b , a} }

record ComonoidalP (_↝_ : Set → Set → Set) : Set where
  field
    ⦃ cocat ⦄ : Category _↝_
    _⊕_ : (A ↝ C) → (B ↝ D) → ((A ⊎ B) ↝ (C ⊎ D))
open ComonoidalP ⦃ … ⦄ public

instance
  →-ComonoidalP : ComonoidalP (λ (A B : Set) → A → B)
  →-ComonoidalP = record {
    _⊕_ = λ { f g → (λ { (inj₁ a) → inj₁ (f a) ; (inj₂ b) → inj₂ (g b) }) } }

record Cocartesian _↝_ : Set where
  field
    ⦃ _↝_ComonoidalP ⦄ : ComonoidalP _↝_
    inl : A ↝ (A ⊎ B)
    inr : B ↝ (A ⊎ B)
    jam : (A ⊎ A) ↝ A
open Cocartesian ⦃ … ⦄ public

_▽_ : ⦃ _ : Cocartesian _↝_ ⦄ → (A ↝ C) → (B ↝ C) → ((A ⊎ B) ↝ C)
f ▽ g = jam ∘ (f ⊕ g)

instance
  →-Cocartesian : Cocartesian (λ (A B : Set) → A → B)
  →-Cocartesian = record {
    inl = inj₁ ;
    inr = inj₂ ;
    jam = λ { (inj₁ a) → a ; (inj₂ a) → a }
   }

record Num (A : Set) : Set where
  field
    _+_ _*_ _-_ : A → A → A
    negate : A → A
    fromℕ : ℕ → A
open Num ⦃ … ⦄ public

-- instance
--   ℕ-Num : Num ℕ
--   ℕ-Num = record {
--      _+_ = _+ℕ_
--    ; _*_ = _*ℕ_
--    ; _-_ = _-ℕ_
--    ; negate = λ b → 0 - b
--    ; fromℕ = id
--    }

record NumCat (_↝_ : Set → Set → Set) (A : Set) : Set where
  field
    _+c_ _*c_ _-c_ : (A × A) ↝ A
    negate-c : A ↝ A
open NumCat ⦃ … ⦄ public

instance
  →-NumCat : ⦃ _ : Num A ⦄ → NumCat (λ (B C : Set) → B → C) A
  →-NumCat = record {
      _+c_ = uncurry _+_
    ; _*c_ = uncurry _*_
    ; _-c_ = uncurry _-_
    ; negate-c = negate
    }

record Closed _↝_ : Set where
  field
    ⦃ _↝_MonoidalP ⦄ : MonoidalP _↝_
    _⇒_ : (A ↝ B) → (C ↝ D) → ((B → C) ↝ (A → D))
open Closed ⦃ … ⦄ public

instance
  →-Closed : Closed (λ (A B : Set) → A → B)
  →-Closed = record {
    _⇒_ = λ { f h g → h ∘ g ∘ f }
   }
