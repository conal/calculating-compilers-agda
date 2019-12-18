{-# OPTIONS --type-in-type --rewriting #-}

open import Data.Product renaming (swap to pswap)
open import Data.Unit
open import Function

open import Relation.Binary.PropositionalEquality as PE hiding (Extensionality)
open PE.≡-Reasoning
-- open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
open import Agda.Builtin.Equality.Rewrite

variable
 A B C D U V Z : Set
 _→k_ : Set → Set → Set

First : Set -> Set -> Set
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
    _∘c_ = _∘′_ ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

id-sf : StackFun A A
id-sf = sf id

_∘sf_ : StackFun B C → StackFun A B → StackFun A C
sf g ∘sf sf f = sf (g ∘ f)

instance
  StackFun-Category : Category StackFun
  StackFun-Category = record {
    idc = id-sf ;
    _∘c_ = _∘sf_ ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

-- Homomorphisms

stackFun-id : stackFun id ≡ id-sf {A}
stackFun-id = refl

stackFun-comp : ∀ {g : B → C} {f : A → B} → stackFun (g ∘ f) ≡ stackFun g ∘sf stackFun f
stackFun-comp = refl

record MonoidalP (_→k_ : Set → Set → Set) : Set where
  field
    _×c_ : (A →k C) → (B →k D) → ((A × B) →k (C × D))
open MonoidalP ⦃ … ⦄

-- _×→_ : (A → C) → (B → D) → ((A × B) → (C × D))
-- (f ×→ g) (a , b) = f a , g b

-- _×sf_ : StackFun A C → StackFun B D → StackFun (A × B) (C × D)
-- sf f ×sf sf g = sf {!!}

instance
  →-MonoidalP : MonoidalP (λ (A B : Set) → A → B)
  →-MonoidalP = record {
    _×c_ = λ { f g (a , b) → f a , g b } }


record AssociativeCat (_→k_ : Set → Set → Set) : Set where
  field
    rassoc : ((A × B) × C) →k (A × (B × C))
    lassoc : (A × (B × C)) →k ((A × B) × C)
open AssociativeCat ⦃ … ⦄

instance
  →-AssociativeCat : AssociativeCat (λ (A B : Set) → A → B)
  →-AssociativeCat = record {
    rassoc = λ { ((a , b) , c) → a , b , c } ;
    lassoc = λ { (a , b , c) → (a , b) , c } }

instance
  StackFun-AssociativeCat : AssociativeCat StackFun
  StackFun-AssociativeCat = record {
    rassoc = stackFun rassoc ;
    lassoc = stackFun lassoc }

record BraidedCat (_→k_ : Set → Set → Set) : Set where
  field
    swap : (A × B) →k (B × A)
open BraidedCat ⦃ … ⦄

instance
  →-BraidedCat : BraidedCat (λ (A B : Set) → A → B)
  →-BraidedCat = record {
    swap = λ {(a , b) → b , a}
    }

-- swap→ : (A × B) → (B × A)
-- swap→ (a , b) = b , a

swapSF : StackFun ((A × B) × C) (A × (B × C))
swapSF = sf (λ {(((a , b) , c) , z) → (a , b , c) , z})

instance
  StackFun-BraidedCat : BraidedCat StackFun
  StackFun-BraidedCat = record {
    swap = stackFun swap
    -- swap = sf (λ {((a , b), z) → (b , a) , z})
     }

firstSF : ∀ {A B C : Set} → StackFun A C → StackFun (A × B) (C × B)
-- firstSF (sf f) = sf (lassoc ∘ f ∘ rassoc)
-- firstSF (sf f) = sf ((λ {(c , (b , z)) → (c , b) , z}) ∘ f ∘ rassoc)
-- firstSF (sf f) = sf (λ {((a , b) , z) → f (a , b) , z})  -- bad
firstSF (sf f) = sf (first f)  -- same bad

stackFun-first : ∀ { f : A → C } → firstSF {B = B} (stackFun f) ≡ stackFun (first f)
-- stackFun-first = refl
stackFun-first = refl

-- -- Synthesized but not what we want:
-- firstSF (sf f) = sf (λ {((a , b) , z) → f (a , b) , z})

secondSF : StackFun B D → StackFun (A × B) (A × D)
secondSF g = swap ∘c firstSF g ∘c swap

_×sf_ : StackFun A C → StackFun B D → StackFun (A × B) (C × D)
f ×sf g = secondSF g ∘c firstSF f

-- -- Synthesized but not what we want
-- sf f ×sf sf g = sf (λ { ((a , b) , z) → f (a , proj₁ (g (b , z))) , z })

instance
  StackFun-MonoidalP : MonoidalP StackFun
  StackFun-MonoidalP = record {
    _×c_ = _×sf_ }


-- Try a variation on the paper in which the "pure" StackOp contains a function
-- rather than an opcode.

data StackOp : Set → Set → Set where
  pure : (A → B) → StackOp (A × Z) (B × Z)
  push : StackOp ((A × B) × Z) (A × (B × Z))
  pop : StackOp (A × (B × Z)) ((A × B) × Z)

evalStackOp : StackOp U V → U → V
evalStackOp (pure f) = first f
evalStackOp push = rassoc
evalStackOp pop = lassoc

infixr 5 _∷_
data StackOps : Set → Set → Set where
  [] : StackOps A A
  _∷_ : StackOp A B → StackOps B C → StackOps A C

-- TODO: generalize StackOps from StackOp to an arbitrary category.

evalStackOps : StackOps U V → U → V
evalStackOps [] = id
evalStackOps (op ∷ rest) = evalStackOps rest ∘ evalStackOp op

infixr 5 _++_
_++_ : StackOps A B → StackOps B C → StackOps A C
[] ++ ops′ = ops′
(op ∷ ops) ++ ops′ = op ∷ (ops ++ ops′)

++-[] : ∀ {p : StackOps A B} → p ++ [] ≡ p
++-[] {p = []} = refl
++-[] {p = x ∷ p} = cong (x ∷_) ++-[]
{-# REWRITE ++-[] #-}

++-++ : ∀ {p : StackOps A B} {p′ : StackOps B C} {p″ : StackOps C D} → p ++ p′ ++ p″ ≡ (p ++ p′) ++ p″
++-++ {p = []} {p′} {p″} = refl
++-++ {p = x ∷ p} {p′} {p″} = cong (x ∷_) (++-++ {p = p} {p′} {p″})
{-# REWRITE ++-++ #-}

evalSO-assoc : ∀ (ops : StackOps A B) (ops′ : StackOps B C) 
             -> evalStackOps (ops ++ ops′) ≡ evalStackOps ops′ ∘ evalStackOps ops
evalSO-assoc [] ops′ = refl
evalSO-assoc (op ∷ ops) ops′ =
  begin
    evalStackOps ((op ∷ ops) ++ ops′)
  ≡⟨⟩
    evalStackOps (op ∷ (ops ++ ops′))
  ≡⟨⟩
    evalStackOps (ops ++ ops′) ∘ evalStackOp op
  ≡⟨ cong (_∘ evalStackOp op) (evalSO-assoc ops ops′) ⟩
    (evalStackOps ops′ ∘ evalStackOps ops) ∘ evalStackOp op
  ≡⟨⟩
    evalStackOps ops′ ∘ (evalStackOps ops ∘ evalStackOp op)
  ≡⟨⟩
    evalStackOps ops′ ∘ evalStackOps (op ∷ ops)
  ∎

record StackProg (A : Set) (B : Set) : Set where
  constructor sp
  field unSP : ∀ {Z : Set} → StackOps (A × Z) (B × Z)

instance
  StackProg-Category : Category StackProg
  StackProg-Category = record {
    idc = sp [] ;
    _∘c_ = λ { (sp g) (sp f) → sp (f ++ g) } ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

progFun : StackProg A B → StackFun A B
progFun (sp ops) = sf (evalStackOps ops)

progFun-id : progFun (idc {A = A}) ≡ idc
progFun-id = refl

{-

progFun-comp : ∀ (g : StackProg B C) (f : StackProg A B) → progFun (g ∘c f) ≡ progFun g ∘c progFun f
progFun-comp (sp g') (sp f') =
  begin
    progFun (sp g' ∘c sp f')
  ≡⟨⟩
    progFun (sp (f' ++ g'))
  ≡⟨⟩
    sf (evalStackOps (f' ++ g'))
  ≡⟨ cong sf (evalSO-assoc f' g') ⟩
    sf (evalStackOps g' ∘ evalStackOps f')
  ≡⟨⟩
    sf (evalStackOps g' ∘ evalStackOps f')
  ≡⟨⟩
    sf (evalStackOps g') ∘c sf (evalStackOps f')
  ≡⟨⟩
    progFun (sp g') ∘c progFun (sp f')
  ∎

-}

-- The "≡⟨ cong sf (evalSO-assoc f' g') ⟩" line yields
-- 
-- A × _Z_938 → C × _Z_938 != {Z : Set} → A × Z → C × Z because one is
-- an implicit function type and the other is an explicit function type
-- when checking that the expression evalSO-assoc f' g' has type
-- (λ {Z} → evalStackOps (f' ++ g')) ≡ _y_934
