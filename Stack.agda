{-# OPTIONS --type-in-type --rewriting #-}

-- {-# OPTIONS --injective-type-constructors #-}

module Stack where

open import Data.Product renaming (swap to pswap)
open import Data.Unit
open import Function hiding (id; _∘_)
open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open PE.≡-Reasoning
open import Agda.Builtin.Equality.Rewrite

open import Classes
open import IxList

private
  variable
   A B C D U V Z : Set
   _→k_ : Set → Set → Set

First : Set → Set → Set
First A B = ∀ {Z : Set} → A × Z → B × Z

first : (A → B) → First A B
first f (a , z) = (f a , z)

record StackFun (A : Set) (B : Set) : Set where
  constructor sf
  field
    unSF : First A B

stackFun : (A → B) → StackFun A B
stackFun f = sf (first f)

runit : A → A × ⊤
runit a = (a , tt)

rcounit : A × ⊤ → A
rcounit (a , tt) = a

evalStackFun : StackFun A B → (A → B)
evalStackFun (sf h) = rcounit ∘ h ∘ runit

evalStackFun_stackFun₁ : ∀ {f : A → B} → evalStackFun (stackFun f) ≡ f
evalStackFun_stackFun₁ = refl

evalStackFun_stackFun₂ : evalStackFun {A}{B} ∘ stackFun ≡ id
evalStackFun_stackFun₂ = refl

instance
  StackFun-Category : Category StackFun
  StackFun-Category = record {
    id = sf id ;
    _∘_ = λ { (sf g) (sf f) → sf (g ∘ f) } ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

-- Homomorphisms

.stackFun-id : stackFun {A} id ≡ id
stackFun-id = refl

.stackFun-∘ : ∀ {g : B → C} {f : A → B}
            → stackFun (g ∘ f) ≡ stackFun g ∘ stackFun f
stackFun-∘ = refl

instance
  StackFun-AssociativeCat : AssociativeCat StackFun
  StackFun-AssociativeCat = record {
    rassoc = stackFun rassoc ;
    lassoc = stackFun lassoc }

instance
  StackFun-BraidedCat : BraidedCat StackFun
  StackFun-BraidedCat = record { swap = stackFun swap }

firstSF : StackFun A C → StackFun (A × B) (C × B)
firstSF (sf f) = sf (lassoc ∘ f ∘ rassoc)

.stackFun-first : ∀ { f : A → C }
                → firstSF {B = B} (stackFun f) ≡ stackFun (first f)
stackFun-first = refl

secondSF : StackFun B D → StackFun (A × B) (A × D)
secondSF g = swap ∘ firstSF g ∘ swap

instance
  StackFun-MonoidalP : MonoidalP StackFun
  StackFun-MonoidalP = record {
    _⊗_ = λ f g → secondSF g ∘ firstSF f }

stackFun-× : ∀ {f : A → C} {g : B → D} → stackFun (f ⊗ g) ≡ stackFun f ⊗ stackFun g
stackFun-× = refl

instance
  StackFun-Cartesian : Cartesian StackFun
  StackFun-Cartesian = record {
    exl = stackFun exl ;
    exr = stackFun exr ;
    dup = stackFun dup }

instance
  →-Num_ : ⦃ _ : Num A ⦄ → NumCat (λ (B C : Set) → B → C) A
  →-Num_ = record {
      _+c_ = uncurry _+_
    ; _*c_ = uncurry _*_
    ; _-c_ = uncurry _-_
    ; negate-c = negate
    }

data Prim : Set → Set → Set where
  ‵exl : Prim (A × B) A
  ‵exr : Prim (A × B) B
  ‵dup : Prim A (A × A)
  ‵swap : Prim (A × B) (B × A)
  -- …
  ‵negate : ⦃ _ : Num A ⦄ → Prim A A
  ‵add ‵sub ‵mul : ⦃ _ : Num A ⦄ → Prim (A × A) A
  -- …

evalPrim : Prim A B → A → B
evalPrim ‵exl = exl
evalPrim ‵exr = exr
evalPrim ‵dup = dup
evalPrim ‵swap = swap
evalPrim ‵negate = negate-c
evalPrim ‵add = _+c_
evalPrim ‵sub = _-c_
evalPrim ‵mul = _*c_

data StackOp : Set → Set → Set where
  prim : Prim A B → StackOp (A × Z) (B × Z)
  push : StackOp ((A × B) × Z) (A × (B × Z))
  pop  : StackOp (A × (B × Z)) ((A × B) × Z)

evalStackOp : StackOp U V → (U → V)
evalStackOp (prim p) = first (evalPrim p)
evalStackOp push = rassoc
evalStackOp pop = lassoc

StackOps : Set → Set → Set
StackOps = IxList StackOp

evalStackOps : StackOps U V → (U → V)
evalStackOps = evalIL evalStackOp

record StackProg (A : Set) (B : Set) : Set where
  constructor sp
  field unSP : ∀ {Z : Set} → StackOps (A × Z) (B × Z)

instance
  StackProg-Category : Category StackProg
  StackProg-Category = record {
    id = sp id ;
    _∘_ = λ { (sp g) (sp f) → sp (g ∘ f) } ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

progFun : StackProg A B → StackFun A B
progFun (sp ops) = sf (evalStackOps ops)

.progFun-id : progFun (id {A = A}) ≡ id
progFun-id = refl

.progFun-∘ : ∀ {g : StackProg B C} {f : StackProg A B}
           → progFun (g ∘ f) ≡ progFun g ∘ progFun f
progFun-∘ = refl

-- The evalIL REWRITE pragmas make progFun-id and progFun-∘ proofs trivial.

primSP : Prim A B → StackProg A B
primSP p = sp [ prim p ]

instance
  StackProg-BraidedCat : BraidedCat StackProg
  StackProg-BraidedCat = record { swap = primSP ‵swap }

firstSP : StackProg A C → StackProg (A × B) (C × B)
firstSP (sp ops) = sp ([ pop ] ∘ ops ∘ [ push ])

secondSP : StackProg B D → StackProg (A × B) (A × D)
secondSP g = swap ∘ firstSP g ∘ swap

instance
  StackProg-MonoidalP : MonoidalP StackProg
  -- StackProg-MonoidalP = record { _⊗_ = _⊗sp_ }
  StackProg-MonoidalP = record {
   _⊗_ = λ f g → secondSP g ∘ firstSP f }

progFun-first : ∀ {f : StackProg A C}
              → progFun (firstSP {B = B} f) ≡ firstSF (progFun f)
progFun-first = refl

progFun-second : ∀ {g : StackProg B D}
               → progFun (secondSP {A = A} g) ≡ secondSF (progFun g)
progFun-second = refl

progFun-× : ∀ {f : StackProg A C} {g : StackProg B D}
          → progFun (f ⊗ g) ≡ progFun f ⊗ progFun g
progFun-× = refl
