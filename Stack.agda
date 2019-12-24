{-# OPTIONS --type-in-type --rewriting #-}

-- {-# OPTIONS --injective-type-constructors #-}

module Stack where

open import Data.Product renaming (swap to pswap)
open import Data.Unit
open import Function
open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open PE.≡-Reasoning
open import Agda.Builtin.Equality.Rewrite

open import Classes ⦃ … ⦄
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

id-sf : StackFun A A
id-sf = sf id

_∘sf_ : StackFun B C → StackFun A B → StackFun A C
sf g ∘sf sf f = sf (g ∘ f)

instance
  _ : Category StackFun
  _ = record {
    idc = id-sf ;
    _∘c_ = _∘sf_ ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

-- Homomorphisms

.stackFun-id : stackFun {A} idc ≡ idc
stackFun-id = refl

.stackFun-∘ : ∀ {g : B → C} {f : A → B}
            → stackFun (g ∘c f) ≡ stackFun g ∘c stackFun f
stackFun-∘ = refl

record MonoidalP (_→k_ : Set → Set → Set) : Set where
  field
    _×c_ : (A →k C) → (B →k D) → ((A × B) →k (C × D))
open MonoidalP ⦃ … ⦄

instance
  _ : MonoidalP (λ (A B : Set) → A → B)
  _ = record {
    _×c_ = λ { f g (a , b) → f a , g b } }

record Cartesian (_→k_ : Set → Set → Set) : Set where
  field
    exl : (A × B) →k A
    exr : (A × B) →k B
    dup : A →k (A × A)
open Cartesian ⦃ … ⦄

instance
  _ : Cartesian (λ (A B : Set) → A → B)
  _ = record {
    exl = proj₁ ;
    exr = proj₂ ;
    dup = λ a → (a , a) }


record AssociativeCat (_→k_ : Set → Set → Set) : Set where
  field
    rassoc : ((A × B) × C) →k (A × (B × C))
    lassoc : (A × (B × C)) →k ((A × B) × C)
open AssociativeCat ⦃ … ⦄

instance
  _ : AssociativeCat (λ (A B : Set) → A → B)
  _ = record {
    rassoc = λ { ((a , b) , c) → a , b , c } ;
    lassoc = λ { (a , b , c) → (a , b) , c } }

instance
  _ : AssociativeCat StackFun
  _ = record {
    rassoc = stackFun rassoc ;
    lassoc = stackFun lassoc }

record BraidedCat (_→k_ : Set → Set → Set) : Set where
  field
    swap : (A × B) →k (B × A)
open BraidedCat ⦃ … ⦄

instance
  _ : BraidedCat (λ (A B : Set) → A → B)
  _ = record { swap = λ {(a , b) → b , a} }

instance
  _ : BraidedCat StackFun
  _ = record { swap = stackFun swap }

firstSF : StackFun A C → StackFun (A × B) (C × B)
firstSF (sf f) = sf (lassoc ∘ f ∘ rassoc)

.stackFun-first : ∀ { f : A → C }
                → firstSF {B = B} (stackFun f) ≡ stackFun (first f)
stackFun-first = refl

secondSF : StackFun B D → StackFun (A × B) (A × D)
secondSF g = swap ∘c firstSF g ∘c swap

_×sf_ : StackFun A C → StackFun B D → StackFun (A × B) (C × D)
f ×sf g = secondSF g ∘c firstSF f

-- -- Synthesized but not what we want
-- sf f ×sf sf g = sf (λ { ((a , b) , z) → f (a , proj₁ (g (b , z))) , z })

instance
  _ : MonoidalP StackFun
  _ = record {
    _×c_ = _×sf_ }

stackFun-× : ∀ {f : A → C} {g : B → D} → stackFun (f ×c g) ≡ stackFun f ×c stackFun g
stackFun-× = refl

instance
  _ : Cartesian StackFun
  _ = record {
    exl = stackFun exl ;
    exr = stackFun exr ;
    dup = stackFun dup }


record Num (A : Set) : Set where
  field
    _+_ _*_ _-_ : A → A → A
    abs signum negate : A → A
    fromℕ : ℕ → A
open Num ⦃ … ⦄

record NumCat (_→k_ : Set → Set → Set) (A : Set) : Set where
  field
    _+c_ _*c_ _-c_ : (A × A) →k A
    negate-c : A →k A
open NumCat ⦃ … ⦄

instance
  _ : ⦃ _ : Num A ⦄ → NumCat (λ (B C : Set) → B → C) A
  _ = record
                   { _+c_ = uncurry _+_
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

instance
  _ : Category (IxList _→k_)
  _ = record {
    idc = [] ;
    _∘c_ = _∘il_ ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

StackOps : Set → Set → Set
StackOps = IxList StackOp

evalStackOps : StackOps U V → (U → V)
evalStackOps = evalIL evalStackOp

record StackProg (A : Set) (B : Set) : Set where
  constructor sp
  field unSP : ∀ {Z : Set} → StackOps (A × Z) (B × Z)

instance
  _ : Category StackProg
  _ = record {
    idc = sp idc ;
    _∘c_ = λ { (sp g) (sp f) → sp (g ∘c f) } ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

progFun : StackProg A B → StackFun A B
progFun (sp ops) = sf (evalStackOps ops)

.progFun-id : progFun (idc {A = A}) ≡ idc
progFun-id = refl

.progFun-∘ : ∀ {g : StackProg B C} {f : StackProg A B}
           → progFun (g ∘c f) ≡ progFun g ∘c progFun f
progFun-∘ = refl

-- The evalIL REWRITE pragmas make progFun-id and progFun-∘ proofs trivial.

primSP : Prim A B → StackProg A B
primSP p = sp [ prim p ]

instance
  _ : BraidedCat StackProg
  _ = record { swap = primSP ‵swap }

firstSP : StackProg A C → StackProg (A × B) (C × B)
firstSP (sp ops) = sp ([ pop ] ∘c ops ∘c [ push ])

secondSP : StackProg B D → StackProg (A × B) (A × D)
secondSP g = swap ∘c firstSP g ∘c swap

_×sp_ : StackProg A C → StackProg B D → StackProg (A × B) (C × D)
f ×sp g = secondSP g ∘c firstSP f

instance
  _ : MonoidalP StackProg
  _ = record { _×c_ = _×sp_ }

progFun-first : ∀ {f : StackProg A C}
              → progFun (firstSP {B = B} f) ≡ firstSF (progFun f)
progFun-first = refl

progFun-second : ∀ {g : StackProg B D}
               → progFun (secondSP {A = A} g) ≡ secondSF (progFun g)
progFun-second = refl

progFun-× : ∀ {f : StackProg A C} {g : StackProg B D}
          → progFun (f ×c g) ≡ progFun f ×c progFun g
progFun-× = refl
