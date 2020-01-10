{-# OPTIONS --type-in-type #-}
-- {-# OPTIONS --rewriting #-}
-- {-# OPTIONS --irrelevant-projections #-}

-- Linear transformations

module Linear where

open import Agda.Builtin.Float renaming (Float to ℝ)

private
  variable
   A B C D S : Set

open import Data.Unit
open import Data.Product using (_×_;_,_)
open import Relation.Binary.PropositionalEquality as PE
-- open PE.≡-Reasoning
-- open import Agda.Builtin.Equality.Rewrite

open import Classes
open import Iso

-- Functors and representable functors. Move elsewhere.
record Functor (F : Set → Set) : Set where
  field
    map : (A → B) → (F A → F B)
open Functor ⦃ … ⦄ public

record Representable (F : Set → Set) : Set where
  field
    Log : Set
    rep : F A ≃ (Log → A)
open Representable ⦃ … ⦄ public

instance
  idFunctor : Functor (λ (B : Set) → B)
  idFunctor = record { map = id }

  -- TODO: define via a new Terminal class
  idRepresentable : {A : Set} → Representable (λ (B : Set) → B)
  idRepresentable {A} = record
    { Log = ⊤
    ; rep = record
        { to = λ z tt → z
        ; from = λ z → z tt
        ; from∘to = refl
        ; to∘from = refl
        }
    }

  →Functor : Functor (λ (B : Set) → A → B)
  →Functor = record { map = _∘_ }

  →Representable : {A : Set} → Representable (λ (B : Set) → A → B)
  →Representable {A} = record { Log = A ; rep = λ {B} → id≃ }

record HasLin (S : Set) (A : Set) : Set where
  field
    RF : Set → Set
    ⦃ repRF ⦄ : Representable RF  -- 
    ≃RF : A ≃ RF S
open HasLin ⦃ … ⦄ public

instance
  ℝ-HasLin : HasLin ℝ ℝ
  ℝ-HasLin = record
    { RF = id
    ; ≃RF = record { to = id ; from = id ; from∘to = refl ; to∘from = refl }
    }

  -- ×-HasLin : {_ : HasLin S A} → {_ : HasLin S B} → HasLin S (A × B)
  -- ×-HasLin {S} {A} {B} {a} {b} = record
  --   { RF = λ Z → RF A Z × RF B Z
  --   ; ≃RF = ?
  --   }
