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
   _→k_ : Set → Set → Set

record Category (_→k_ : Set → Set → Set) : Set where
  infixr 5 _∘_
  field
    id   : A →k A
    _∘_  : (B →k C) → (A →k B) → (A →k C)
    .id-l  : ∀ {f : A →k B} → id ∘ f ≡ f
    .id-r  : ∀ {f : A →k B} → f ∘ id ≡ f
    .assoc : ∀ {h : C →k D} {g : B →k C} {f : A →k B}
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

record MonoidalP (_→k_ : Set → Set → Set) : Set where
  field
    ⦃ cat ⦄ : Category _→k_
    _⊗_ : (A →k C) → (B →k D) → ((A × B) →k (C × D))
open MonoidalP ⦃ … ⦄ public

instance
  →-MonoidalP : MonoidalP (λ (A B : Set) → A → B)
  →-MonoidalP = record {
    _⊗_ = λ { f g (a , b) → (f a , g b) } }

record Cartesian _→k_ : Set where
  field
    ⦃ _→k_MonoidalP ⦄ : MonoidalP _→k_
    exl : (A × B) →k A
    exr : (A × B) →k B
    dup : A →k (A × A)
open Cartesian ⦃ … ⦄ public

_△_ : ⦃ _ : Cartesian _→k_ ⦄ → (A →k C) → (A →k D) → (A →k (C × D))
f △ g = (f ⊗ g) ∘ dup

instance
  →-Cartesian : Cartesian (λ (A B : Set) → A → B)
  →-Cartesian = record {
    exl = proj₁ ;
    exr = proj₂ ;
    dup = λ a → (a , a) }

record AssociativeCat (_→k_ : Set → Set → Set) : Set where
  field
    rassoc : ((A × B) × C) →k (A × (B × C))
    lassoc : (A × (B × C)) →k ((A × B) × C)
open AssociativeCat ⦃ … ⦄ public

instance
  →-AssociativeCat : AssociativeCat (λ (A B : Set) → A → B)
  →-AssociativeCat = record {
    rassoc = λ { ((a , b) , c) → a , b , c } ;
    lassoc = λ { (a , b , c) → (a , b) , c } }

record BraidedCat (_→k_ : Set → Set → Set) : Set where
  field
    swap : (A × B) →k (B × A)
open BraidedCat ⦃ … ⦄ public

instance
  →-BraidedCat : BraidedCat (λ (A B : Set) → A → B)
  →-BraidedCat = record { swap = λ {(a , b) → b , a} }

record ComonoidalP (_→k_ : Set → Set → Set) : Set where
  field
    ⦃ cocat ⦄ : Category _→k_
    _⊕_ : (A →k C) → (B →k D) → ((A ⊎ B) →k (C ⊎ D))
open ComonoidalP ⦃ … ⦄ public

instance
  →-ComonoidalP : ComonoidalP (λ (A B : Set) → A → B)
  →-ComonoidalP = record {
    _⊕_ = λ { f g → (λ { (inj₁ a) → inj₁ (f a) ; (inj₂ b) → inj₂ (g b) }) } }

record Cocartesian _→k_ : Set where
  field
    ⦃ _→k_ComonoidalP ⦄ : ComonoidalP _→k_
    inl : A →k (A ⊎ B)
    inr : B →k (A ⊎ B)
    jam : (A ⊎ A) →k A
open Cocartesian ⦃ … ⦄ public

_▽_ : ⦃ _ : Cocartesian _→k_ ⦄ → (A →k C) → (B →k C) → ((A ⊎ B) →k C)
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

record NumCat (_→k_ : Set → Set → Set) (A : Set) : Set where
  field
    _+c_ _*c_ _-c_ : (A × A) →k A
    negate-c : A →k A
open NumCat ⦃ … ⦄ public

instance
  →-NumCat : ⦃ _ : Num A ⦄ → NumCat (λ (B C : Set) → B → C) A
  →-NumCat = record {
      _+c_ = uncurry _+_
    ; _*c_ = uncurry _*_
    ; _-c_ = uncurry _-_
    ; negate-c = negate
    }

record Closed _→k_ : Set where
  field
    ⦃ _→k_MonoidalP ⦄ : MonoidalP _→k_
    _⇒_ : (A →k B) → (C →k D) → ((B → C) →k (A → D))
open Closed ⦃ … ⦄ public

instance
  →-Closed : Closed (λ (A B : Set) → A → B)
  →-Closed = record {
    _⇒_ = λ { f h g → h ∘ g ∘ f }
   }
