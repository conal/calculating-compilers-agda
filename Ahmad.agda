{-# OPTIONS --type-in-type --rewriting #-}
-- Type in Type currently needed for impredicative parametericity as in Haskell.
-- Due to the high-level quantification, even with levels/universe polymorphism we need --omega-in-omega

module Ahmad where

open import Data.Sum renaming (swap to sswap)
open import Data.Product renaming (swap to pswap)
open import Data.Unit
open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Function
open import Level
open import Relation.Binary.PropositionalEquality as PE hiding (Extensionality)
open PE.≡-Reasoning
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
open import Agda.Builtin.Equality.Rewrite

variable
 A B C D U V Z : Set
 _→k_ : Set → Set → Set

postulate
  .extensionality : ∀ {α β} → Extensionality α β
  .extensionality-imp : ∀ {α β} → ExtensionalityImplicit α β

-- Section 1

first : (A → B) → (∀ {Z : Set} → A × Z → B × Z)
first f (a , z) = (f a , z)

data StackFun (A : Set) (B : Set) : Set where
  sf : (∀ {Z : Set} → A × Z → B × Z) → StackFun A B

stackFun : (A → B) → StackFun A B
stackFun f = sf (first f)

record UnitCat (_→k_ : Set → Set → Set) : Set where
  field
    lunit : A →k (⊤ × A)
    lcounit : (⊤ × A) →k A
    runit : A →k (A × ⊤)
    rcounit : (A × ⊤) →k A
open UnitCat ⦃ … ⦄

instance
  →-UnitCat : UnitCat (λ (A B : Set) → A → B)
  →-UnitCat = record {
    lunit = λ a → tt , a ;
    lcounit = λ { (tt , a) → a };
    runit = λ a → a , tt ;
    rcounit = λ { (a , tt) → a } }

evalStackFun : StackFun A B → (A → B)
evalStackFun (sf f) = rcounit ∘ f ∘ runit

record Category (_→k_ : Set → Set → Set) : Set where
  infixr 5 _∘c_
  field
    idc   : A →k A
    _∘c_  : (B →k C) → (A →k B) → (A →k C)
    .id-l  : ∀ {f : A →k B} → idc ∘c f ≡ f
    .id-r  : ∀ {f : A →k B} → f ∘c idc ≡ f
    .assoc : ∀ {h : C →k D} {g : B →k C} {f : A →k B} → (h ∘c g) ∘c f ≡ h ∘c (g ∘c f)
open Category ⦃ … ⦄

instance
  →-Category : Category (λ (A B : Set) → A → B)
  →-Category = record {
    idc = id ;
    _∘c_ = λ f g → f ∘ g ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

id-sf : StackFun A A
id-sf = sf id

.id-sf-homomorph : id-sf {A} ≡ stackFun id
id-sf-homomorph = begin
                  id-sf ≡⟨ refl ⟩
                  sf id ≡⟨ cong sf (extensionality-imp λ {Z} → extensionality λ { (x , z) → refl }) ⟩
                  sf (first id) ≡⟨ refl ⟩
                  stackFun id ∎

_∘sf_ : StackFun B C → StackFun A B → StackFun A C
(sf g) ∘sf (sf f) =  sf (g ∘ f)
-- Strengthening step/surjectivity lemma seems to require parametricity which is only supported in an expertimental branch of Agda

.∘-sf-homomorph : ∀ {g : B → C} {f : A → B} → stackFun g ∘sf stackFun f ≡ stackFun (g ∘ f)
∘-sf-homomorph {g = g} {f = f} = begin
                                 (stackFun g ∘sf stackFun f) ≡⟨ refl ⟩
                                 (sf (first g) ∘sf sf (first f)) ≡⟨ refl ⟩
                                 sf (first g ∘ first f) ≡⟨ cong sf (extensionality-imp λ {Z} → extensionality λ { (x , z) → refl }) ⟩
                                 sf (first (g ∘ f)) ≡⟨ refl ⟩
                                 stackFun (g ∘ f) ∎

instance
  StackFun-Category : Category StackFun
  StackFun-Category = record {
    idc = id-sf ;
    _∘c_ = _∘sf_ ;
    id-l = λ { {f = sf f} → refl } ;
    id-r = λ { {f = sf f} → refl } ;
    assoc = λ { {h = sf h} {g = sf g} {f = sf f} → refl } }

record AssociativeCat (_→k_ : Set → Set → Set) : Set where
  field
    rassoc : ((A × B) × C) →k (A × (B × C))
    lassoc : (A × (B × C)) →k ((A × B) × C)
open AssociativeCat ⦃ … ⦄

record BraidedCat (_→k_ : Set → Set → Set) : Set where
  field
    swap : (A × B) →k (B × A)
open BraidedCat ⦃ … ⦄

instance
  →-AssociativeCat : AssociativeCat (λ (A B : Set) → A → B)
  →-AssociativeCat = record {
    rassoc = λ { ((a , b) , c) → a , b , c } ;
    lassoc = λ { (a , b , c) → (a , b) , c } }

instance
  →-BraidedCat : BraidedCat (λ (A B : Set) → A → B)
  →-BraidedCat = record {
    swap = λ { (a , b) → b , a } }

instance
  StackFun-AssociativeCat : AssociativeCat StackFun
  StackFun-AssociativeCat = record {
    rassoc = stackFun rassoc ;
    lassoc = stackFun lassoc }

instance
  StackFun-BraidedCat : BraidedCat StackFun
  StackFun-BraidedCat = record {
    swap = stackFun swap }

record MonoidalP (_→k_ : Set → Set → Set) : Set where
  field
    _×m_ : (A →k C) → (B →k D) → ((A × B) →k (C × D))
open MonoidalP ⦃ … ⦄

firstP : ∀ ⦃ c-→k : Category _→k_ ⦄ ⦃ mp-→k : MonoidalP _→k_ ⦄ →
         (A →k C) → ((A × B) →k (C × B))
firstP f = f ×m idc

secondP :  ∀ ⦃ c-→k : Category _→k_ ⦄ ⦃ mp-→k : MonoidalP _→k_ ⦄ →
           (B →k D) → ((A × B) →k (A × D))
secondP g = idc ×m g

firstSF : StackFun A C → StackFun (A × B) (C × B)
firstSF (sf f) = sf (lassoc ∘ f ∘ rassoc)

secondSF : StackFun B D → StackFun (A × B) (A × D)
secondSF g = swap ∘c firstSF g ∘c swap

instance
  →-MonoidalP : MonoidalP (λ (A B : Set) → A → B)
  →-MonoidalP = record {
    _×m_ = λ { f g (a , b) → f a , g b } }

instance
  StackFun-MonoidalP : MonoidalP StackFun
  StackFun-MonoidalP = record { _×m_ = λ f g → firstSF f ∘c secondSF g }

record Cartesian (_→k_ : Set → Set → Set) : Set where
  field
    exl : (A × B) →k A
    exr : (A × B) →k B
    dup : A →k (A × A)
open Cartesian ⦃ … ⦄

instance
  →-Cartesian : Cartesian (λ (A B : Set) → A → B)
  →-Cartesian = record {
    exl = proj₁ ;
    exr = proj₂ ;
    dup = λ a → (a , a) }

instance
  StackFun-Cartesian : Cartesian StackFun
  StackFun-Cartesian = record {
    exl = stackFun exl ;
    exr = stackFun exr ;
    dup = stackFun dup }

_▵_ : ⦃ cat-→k : Category _→k_ ⦄ ⦃ mp-→k : MonoidalP _→k_ ⦄ ⦃ cart-→k : Cartesian _→k_ ⦄ →
      (A →k C) → (A →k D) → (A →k (C × D))
f ▵ g = (f ×m g) ∘c dup

record MonoidalS (_→k_ : Set → Set → Set) : Set where
  field
    _+m_ : (A →k C) → (B →k D) → ((A ⊎ B) →k (C ⊎ D))
open MonoidalS ⦃ … ⦄

instance
  →-MonoidalS : MonoidalS (λ (A B : Set) → A → B)
  →-MonoidalS = record {
    _+m_ = λ { f g (inj₁ a) → inj₁ (f a) ; f g (inj₂ b) → inj₂ (g b) } }

record Cocartesian (_→k_ : Set → Set → Set) : Set where
  field
    inl : A →k (A ⊎ B)
    inr : B →k (A ⊎ B)
    jam : (A ⊎ A) →k A
open Cocartesian ⦃ … ⦄

instance
  →-Cocartesian : Cocartesian (λ (A B : Set) → A → B)
  →-Cocartesian = record {
    inl = inj₁ ;
    inr = inj₂ ;
    jam = λ { (inj₁ a) → a ; (inj₂ b) → b } }

instance
  StackFun-Cocartesian : Cocartesian StackFun
  StackFun-Cocartesian = record {
    inl = stackFun inl ;
    inr = stackFun inr ;
    jam = stackFun jam }

_▿_ :  ⦃ cat-→k : Category _→k_ ⦄ ⦃ ms-→k : MonoidalS _→k_ ⦄ ⦃ ccrt-→k : Cocartesian _→k_ ⦄ →
       (A →k C) → (B →k C) → ((A ⊎ B) →k C)
f ▿ g = jam ∘c (f +m g)

record Distributive (_→k_ : Set → Set → Set) : Set where
  field
    ⦃ cart-→k ⦄ : Cartesian _→k_
    ⦃ ccrt-→k ⦄ : Cocartesian _→k_
    distl : (A × (U ⊎ V)) →k ((A × U) ⊎ (A × V))
  open Cartesian cart-→k
  open Cocartesian ccrt-→k
open Distributive ⦃ … ⦄

distr : ∀ ⦃ c-→k : Category _→k_ ⦄ ⦃ mp-→k : MonoidalP _→k_ ⦄ ⦃ ms-→k : MonoidalS _→k_ ⦄
          ⦃ bc-→k : BraidedCat _→k_ ⦄ ⦃ dist-→k : Distributive _→k_ ⦄ →
       ((U ⊎ V) × B) →k ((U × B) ⊎ (V × B))
distr = (swap +m swap) ∘c distl ∘c swap

undistl : ∀  ⦃ c-→k : Category _→k_ ⦄ ⦃ mp-→k : MonoidalP _→k_ ⦄ ⦃ ms-→k : MonoidalS _→k_ ⦄
             ⦃ ccrt-→k : Cocartesian _→k_ ⦄ →
          ((A × U) ⊎ (A × V)) →k (A × (U ⊎ V))
undistl = secondP inl ▿ secondP inr

undistr : ∀  ⦃ c-→k : Category _→k_ ⦄ ⦃ mp-→k : MonoidalP _→k_ ⦄ ⦃ ms-→k : MonoidalS _→k_ ⦄
             ⦃ ccrt-→k : Cocartesian _→k_ ⦄ →
          ((U × B) ⊎ (V × B)) →k ((U ⊎ V) × B)
undistr = firstP inl ▿ firstP inr

instance
  →-Distributive : Distributive (λ (A B : Set) → A → B)
  →-Distributive = record {
    distl = λ { (a , inj₁ u) → inj₁ (a , u) ; (a , inj₂ v) → inj₂ (a , v) } }

instance
  StackFun-Distributive : Distributive StackFun
  StackFun-Distributive = record {
    distl = stackFun distl }

instance
  StackFun-MonoidalS : MonoidalS StackFun
  StackFun-MonoidalS = record {
    _+m_ = λ { (sf f) (sf g) → sf (undistr ∘ (f +m g) ∘ distr) } }


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
  →-Num-NumCat : ⦃ num : Num A ⦄ → NumCat (λ (B C : Set) → B → C) A
  →-Num-NumCat = record
                   { _+c_ = uncurry _+_
                   ; _*c_ = uncurry _*_
                   ; _-c_ = uncurry _-_
                   ; negate-c = negate
                   }

-- Section 2
data Prim : Set → Set → Set where
  ‵exl : Prim (A × B) A
  ‵exr : Prim (A × B) B
  ‵dup : Prim A (A × A)
  ‵swap : Prim (A × B) (B × A)
  -- …
  ‵negate : ⦃ num : Num A ⦄ → Prim A A
  ‵add ‵sub ‵mul : ⦃ num : Num A ⦄ → Prim (A × A) A
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
  ‵prim : Prim A B → StackOp (A × Z) (B × Z)
  ‵push : StackOp ((A × B) × Z) (A × (B × Z))
  ‵pop : StackOp (A × (B × Z)) ((A × B) × Z)

evalStackOp : StackOp U V → U → V
evalStackOp (‵prim f) = first (evalPrim f)
evalStackOp ‵push = rassoc
evalStackOp ‵pop = lassoc

infixr 5 _◂_
data StackOps : Set → Set → Set where
  [] : StackOps A A
  _◂_ : StackOp A B → StackOps B C → StackOps A C

evalStackOps : StackOps U V → U → V
evalStackOps [] = id
evalStackOps (op ◂ rest) = evalStackOps rest ∘ evalStackOp op

infixr 5 _++_
_++_ : StackOps A B → StackOps B C → StackOps A C
[] ++ ops′ = ops′
(op ◂ ops) ++ ops′ = op ◂ (ops ++ ops′)

++-[] : ∀ {p : StackOps A B} → p ++ [] ≡ p
++-[] {p = []} = refl
++-[] {p = x ◂ p} = cong (x ◂_) ++-[]
{-# REWRITE ++-[] #-}

++-++ : ∀ {p : StackOps A B} {p′ : StackOps B C} {p″ : StackOps C D} → p ++ p′ ++ p″ ≡ (p ++ p′) ++ p″
++-++ {p = []} {p′} {p″} = refl
++-++ {p = x ◂ p} {p′} {p″} = cong (x ◂_) (++-++ {p = p} {p′} {p″})
{-# REWRITE ++-++ #-}

data StackProg (A : Set) (B : Set) : Set where
  sp : (∀ {Z : Set}  → StackOps (A × Z) (B × Z)) → StackProg A B

instance
  StackProg-Category : Category StackProg
  StackProg-Category = record {
    idc = sp [] ;
    _∘c_ = λ { (sp g) (sp f) → sp (f ++ g) } ;
    id-l = λ { {f = sp f} → refl } ;
    id-r = λ { {f = sp f} → refl } ;
    assoc = λ { {h = sp h} {g = sp g} {f = sp f} → refl } }

primProg : Prim A B → StackProg A B
primProg p = sp (‵prim p ◂ [])

instance
  StackProg-BraidedCat : BraidedCat StackProg
  StackProg-BraidedCat = record {
    swap = primProg ‵swap }


firstSP : StackProg A C → StackProg (A × B) (C × B)
firstSP (sp ops) = sp (‵push ◂ ops ++ ‵pop ◂ [])

secondSP : StackProg B D → StackProg (A × B) (A × D)
secondSP g = swap ∘c firstSP g ∘c swap

instance
  StackProg-MonoidalP : MonoidalP StackProg
  StackProg-MonoidalP = record {
    _×m_ = λ f g → firstSP f ∘c secondSP g }

instance
  StackProg-Cartesian : Cartesian StackProg
  StackProg-Cartesian = record {
    exl = primProg ‵exl ;
    exr = primProg ‵exr ;
    dup = primProg ‵dup }

instance
  StackProg-NumCat : ⦃ num : Num A ⦄ → NumCat StackProg A
  StackProg-NumCat = record
                       { _+c_ = primProg ‵add
                       ; _*c_ = primProg ‵mul
                       ; _-c_ = primProg ‵sub
                       ; negate-c = primProg ‵negate
                       }

progFun : StackProg A B → StackFun A B
progFun (sp ops) = sf (evalStackOps ops)

evalProg : StackProg A B → A → B
evalProg = evalStackFun ∘ progFun
