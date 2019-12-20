{-# OPTIONS --type-in-type --rewriting #-}

open import Data.Product renaming (swap to pswap)
open import Data.Unit
open import Function

open import Relation.Binary.PropositionalEquality as PE hiding (Extensionality)
open PE.≡-Reasoning
open import Axiom.Extensionality.Propositional
       using (Extensionality; ExtensionalityImplicit)
open import Agda.Builtin.Equality.Rewrite

variable
 A B C D U V Z : Set
 _→k_ : Set → Set → Set

postulate
  .ext : ∀ {α β} → Extensionality α β
  .ext-i : ∀ {α β} → ExtensionalityImplicit α β

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
    .assoc : ∀ {h : C →k D} {g : B →k C} {f : A →k B}
           → (h ∘c g) ∘c f ≡ h ∘c (g ∘c f)
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

.stackFun-id : stackFun id ≡ id-sf {A}
stackFun-id = refl

.stackFun-comp : ∀ {g : B → C} {f : A → B}
               → stackFun (g ∘ f) ≡ stackFun g ∘sf stackFun f
stackFun-comp = refl

record MonoidalP (_→k_ : Set → Set → Set) : Set where
  field
    _×c_ : (A →k C) → (B →k D) → ((A × B) →k (C × D))
open MonoidalP ⦃ … ⦄

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

firstSF : StackFun A C → StackFun (A × B) (C × B)
firstSF (sf f) = sf (lassoc ∘ f ∘ rassoc)
-- firstSF (sf f) = sf (first f)  -- bad

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
  StackFun-MonoidalP : MonoidalP StackFun
  StackFun-MonoidalP = record {
    _×c_ = _×sf_ }

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

infixr 5 _∘so_
_∘so_ : StackOps B C → StackOps A B → StackOps A C
ops′ ∘so [] = ops′
ops′ ∘so (op ∷ ops) = op ∷ (ops′ ∘so ops)

.∘so-id : ∀ (p : StackOps A B) → [] ∘so p ≡ p
∘so-id [] = refl
∘so-id (x ∷ p) = cong (x ∷_) (∘so-id p)
{-# REWRITE ∘so-id #-}

.∘so-assoc : ∀ (p : StackOps A B) (p′ : StackOps B C) (p″ : StackOps C D)
          → p″ ∘so (p′ ∘so p) ≡ (p″ ∘so p′) ∘so p
∘so-assoc [] _ _ = refl
∘so-assoc (x ∷ p) p′ p″ = cong (x ∷_) (∘so-assoc p p′ p″)
{-# REWRITE ∘so-assoc #-}

instance
  so-Category : Category StackOps
  so-Category = record {
    idc = [] ;
    _∘c_ = _∘so_ ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

.evalSO-id : evalStackOps {A} idc ≡ idc
evalSO-id = refl

.evalSO-comp : ∀ (f : StackOps A B) (g : StackOps B C)
             -> evalStackOps (g ∘c f) ≡ evalStackOps g ∘c evalStackOps f
evalSO-comp [] g = refl
evalSO-comp (op ∷ f) g =
  begin
    evalStackOps (g ∘c (op ∷ f))
  ≡⟨⟩
    evalStackOps (op ∷ (g ∘c f))
  ≡⟨⟩
    evalStackOps (g ∘c f) ∘ evalStackOp op
  ≡⟨ cong (_∘ evalStackOp op) (evalSO-comp f g) ⟩
    (evalStackOps g ∘ evalStackOps f) ∘ evalStackOp op
  ≡⟨⟩
    evalStackOps g ∘ (evalStackOps f ∘ evalStackOp op)
  ≡⟨⟩
    evalStackOps g ∘ evalStackOps (op ∷ f)
  ∎
{-# REWRITE evalSO-comp #-}

-- Given "evalSO-comp _ _ = {! !}", Agda will fill the hole with refl, and then
-- complain:
-- 
--   A != B of type Set
--   when checking that the expression refl has type
--   evalStackOps (g ∘so f) ≡ (λ x → evalStackOps g (evalStackOps f x))
--
-- Bug?

record StackProg (A : Set) (B : Set) : Set where
  constructor sp
  field unSP : ∀ {Z : Set} → StackOps (A × Z) (B × Z)

instance
  StackProg-Category : Category StackProg
  StackProg-Category = record {
    idc = sp idc ;
    _∘c_ = λ { (sp g) (sp f) → sp (g ∘c f) } ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

progFun : StackProg A B → StackFun A B
progFun (sp ops) = sf (evalStackOps ops)

.progFun-id : progFun (idc {A = A}) ≡ idc
progFun-id = refl

-- .progFun-comp : ∀ (g : StackProg B C) (f : StackProg A B)
--               → progFun (g ∘c f) ≡ progFun g ∘c progFun f
-- progFun-comp (sp g') (sp f') =
--   begin
--     progFun (sp g' ∘c sp f')
--   ≡⟨⟩
--     progFun (sp (g' ∘c f'))
--   ≡⟨⟩
--     sf (evalStackOps (g' ∘c f'))
--   ≡⟨ cong sf (ext-i (evalSO-comp f' g')) ⟩
--     sf (evalStackOps g' ∘ evalStackOps f')
--   ≡⟨⟩
--     sf (evalStackOps g' ∘ evalStackOps f')
--   ≡⟨⟩
--     sf (evalStackOps g') ∘c sf (evalStackOps f')
--   ≡⟨⟩
--     progFun (sp g') ∘c progFun (sp f')
--   ∎

-- With the evalSO-comp REWRITE pragma, the proof becomes trivial:

.progFun-comp : ∀ {g : StackProg B C} {f : StackProg A B}
              → progFun (g ∘c f) ≡ progFun g ∘c progFun f
progFun-comp = refl



-- firstSP : StackProg A C → StackProg (A × B) (C × B)
-- firstSP (sp (op ∷ ops)) = sp ((pop ∷ []) ∘so ops ∘so (push ∷ []))
-- 
--  /Users/conal/Agda/Stack/Stack.agda:305,14-22
--  Cannot split on argument of non-datatype
--  {Z : Set} → StackOps (A × Z) (C × Z)
--  when checking that the pattern op ∷ ops has type
--  {Z : Set} → StackOps (A × Z) (C × Z)

-- Simpler (I think): the underlying first on StackOps:

-- firstSO : StackOps (A × Z) (C × Z) → StackOps ((A × B) × Z) ((C × B) × Z)
-- firstSO ops = {!!}

-- When I try to case split on ops, I get:
--
--   I'm not sure if there should be a case for the constructor [],
--   because I get stuck when trying to solve the following unification
--   problems (inferred index ≟ expected index):
--     A₁ ≟ A₂ × Z₁
--     A₁ ≟ C₁ × Z₁
--   when checking that the expression ? has type
--   StackOps ((A × B) × Z) ((C × B) × Z)
