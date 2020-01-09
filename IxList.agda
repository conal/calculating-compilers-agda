{-# OPTIONS --type-in-type --rewriting #-}

-- Lists of composable "arrows"

module IxList where

open import Relation.Binary.PropositionalEquality as PE
       hiding (Extensionality; [_])
open PE.≡-Reasoning
open import Agda.Builtin.Equality.Rewrite

open import Classes

private
  variable
   A B C D U V : Set
   _→k_ : Set → Set → Set

infixr 5 _∷_
data IxList : (Set → Set → Set) → (Set → Set → Set) where
  [] : IxList _→k_ A A
  _∷_ : (A →k B) → IxList _→k_ B C → IxList _→k_ A C

infixr 5 _∘il_
_∘il_ : IxList _→k_ B C → IxList _→k_ A B → IxList _→k_ A C
ops′ ∘il [] = ops′
ops′ ∘il (op ∷ ops) = op ∷ (ops′ ∘il ops)

.∘il-id : ∀ (p : IxList _→k_ A B) → [] ∘il p ≡ p
∘il-id [] = refl
∘il-id (x ∷ p) = cong (x ∷_) (∘il-id p)
{-# REWRITE ∘il-id #-}

.∘il-assoc : ∀ (p : IxList _→k_ A B) (p′ : IxList _→k_ B C) (p″ : IxList _→k_ C D)
           → p″ ∘il (p′ ∘il p) ≡ (p″ ∘il p′) ∘il p
∘il-assoc [] _ _ = refl
∘il-assoc (x ∷ p) p′ p″ = cong (x ∷_) (∘il-assoc p p′ p″)
{-# REWRITE ∘il-assoc #-}

instance
  IxList-Category : Category (IxList _→k_)
  IxList-Category = record {
    id = [] ;
    _∘_ = _∘il_ ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

evalIL : (∀ {a b} → (a →k b) → (a → b)) → IxList _→k_ U V → (U → V)
evalIL ev [] = id
evalIL ev (op ∷ ops) = evalIL ev ops ∘ ev op

.evalIL-id : ∀ (ev : ∀ {U V} → (U →k V) → (U → V)) → evalIL {U = U} ev [] ≡ id
evalIL-id _ = refl

.evalIL-∘ : ∀ (ev : ∀ {U V} → (U →k V) → (U → V)) → (f : IxList _→k_ A B) (g : IxList _→k_ B C) 
          → evalIL ev (g ∘il f) ≡ evalIL ev g ∘ evalIL ev f
evalIL-∘ ev [] g = refl
evalIL-∘ ev (op ∷ f) g =
  begin
    evalIL ev (g ∘il (op ∷ f))
  ≡⟨⟩
    evalIL ev (op ∷ (g ∘il f))
  ≡⟨⟩
    evalIL ev (g ∘il f) ∘ ev op
  ≡⟨ cong (_∘ ev op) (evalIL-∘ ev f g) ⟩
    (evalIL ev g ∘ evalIL ev f) ∘ ev op
  ≡⟨⟩
    evalIL ev g ∘ (evalIL ev f ∘ ev op)
  ≡⟨⟩
    evalIL ev g ∘ evalIL ev (op ∷ f)
  ∎
{-# REWRITE evalIL-∘ #-}

-- TODO: Can we automate the evalIL-∘ proof by using the REWRITE recursively?

[_] : (A →k B) → IxList _→k_ A B
[ op ] = op ∷ []
