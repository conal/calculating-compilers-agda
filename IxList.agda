{-# OPTIONS --type-in-type --rewriting #-}

-- Lists of composable "arrows"

module IxList where

open import Relation.Binary.PropositionalEquality as PE
       hiding (Extensionality; [_])
open import Agda.Builtin.Equality.Rewrite

private
  variable
   A B C D : Set
   _→k_ : Set → Set → Set

infixr 5 _∷_
data IxList : (Set → Set → Set) → (Set → Set → Set) where
  [] : IxList _→k_ A A
  _∷_ : (A →k B) → IxList _→k_ B C → IxList _→k_ A C

[_] : (A →k B) → IxList _→k_ A B
[ op ] = op ∷ []

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
