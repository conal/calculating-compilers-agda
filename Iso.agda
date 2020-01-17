{-# OPTIONS --type-in-type --rewriting #-}
{-# OPTIONS --irrelevant-projections #-}

-- Isomorphisms, as in PLFA

module Iso where

private
  variable
   A B C D : Set

open import Data.Product using (_×_;_,_)
open import Relation.Binary.PropositionalEquality as PE
open PE.≡-Reasoning
open import Agda.Builtin.Equality.Rewrite

open import Classes

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    .from∘to : ∀ {x : A} → from (to x) ≡ x
    .to∘from : ∀ {y : B} → to (from y) ≡ y
open _≃_ public

-- {-# REWRITE from∘to #-}
-- {-# REWRITE to∘from #-}

--   "from∘to is not a legal rewrite rule, since the left-hand side is neither a
--   defined symbol nor a constructor when checking the pragma REWRITE from∘to"

-- If we could make from∘to and to∘from into rewrite rules, I think the explicit
-- equational proofs below could all be replaced by refl. Is there a way?
-- Apparently not. See https://github.com/conal/calculating-compilers-agda/issues/5
-- and https://github.com/agda/agda/issues/4369 .


_⁻¹ : (A ≃ B) → (B ≃ A)
A≃B ⁻¹ = record { to = from A≃B; from = to A≃B; from∘to = to∘from A≃B; to∘from = from∘to A≃B }

id≃ : A ≃ A
id≃ =
  record { to = id
         ; from = id
         ; from∘to = refl
         ; to∘from = refl
         }

_∘≃_ : (B ≃ C) → (A ≃ B) → (A ≃ C)
B≃C ∘≃ A≃B =
  record { to = to B≃C ∘ to A≃B
         ; from = from A≃B ∘ from B≃C
         ; from∘to = λ { { x } →
             begin
               (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
             ≡⟨⟩
               from A≃B (from B≃C (to B≃C (to A≃B x)))
             ≡⟨ cong (from A≃B) (from∘to B≃C) ⟩
               from A≃B (to A≃B x)
             ≡⟨ from∘to A≃B ⟩
               x
             ∎ }
         ; to∘from = λ { {y} →
             begin
               (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y) 
             ≡⟨⟩
               to B≃C (to A≃B (from A≃B (from B≃C y)))
             ≡⟨ cong (to B≃C) (to∘from A≃B) ⟩
               to B≃C (from B≃C y)
             ≡⟨ to∘from B≃C ⟩
               y
             ∎ }
         }

-- --irrelevant-projections needed for from∘to and to∘from. Alternatives?

instance
  ≃-Category : Category _≃_
  ≃-Category =
   record { id = id≃
          ; _∘_ = _∘≃_
          ; id-l = refl
          ; id-r = refl
          ; assoc = refl
          }

_⊗≡_ : ∀ {a a′ : A} {b b′ : B} → a ≡ a′ → b ≡ b′ → (a , b) ≡ (a′ , b′)
_⊗≡_ {A} {B} {a} {a′} {b} {b′} a≡a′ b≡b′ =
  begin
    (a , b)
  ≡⟨ cong (_,_ a) b≡b′ ⟩
    (a , b′)
  ≡⟨ cong (λ z → z , b′) a≡a′ ⟩
    (a′ , b′)
  ∎

_⊗≃_ : (A ≃ C) → (B ≃ D) → (A × B ≃ C × D)
A≃C ⊗≃ B≃D =
  record { to = to A≃C ⊗ to B≃D
         ; from = from A≃C ⊗ from B≃D
         ; from∘to = λ { {(a , b)} →
             begin
               (from A≃C ⊗ from B≃D) ((to A≃C ⊗ to B≃D) (a , b))
             ≡⟨⟩
               (from A≃C ⊗ from B≃D) (to A≃C a , to B≃D b)
             ≡⟨⟩
               (from A≃C (to A≃C a) , from B≃D (to B≃D b))
             ≡⟨ from∘to A≃C ⊗≡ from∘to B≃D ⟩
               (a , b)
             ∎ }
         ; to∘from = λ { {(c , d)} →
             begin
               (to A≃C ⊗ to B≃D) ((from A≃C ⊗ from B≃D) (c , d))
             ≡⟨⟩
               (to A≃C ⊗ to B≃D) (from A≃C c , from B≃D d)
             ≡⟨⟩
               (to A≃C (from A≃C c) , to B≃D (from B≃D d))
             ≡⟨ to∘from A≃C ⊗≡ to∘from B≃D ⟩
               (c , d)
             ∎ }
         }

instance
  ≃-MonoidalP : MonoidalP _≃_
  ≃-MonoidalP = record { _⊗_ = _⊗≃_ }

instance
  ≃-AssociativeCat : AssociativeCat _≃_
  ≃-AssociativeCat = record
      { rassoc = record { to = rassoc
                        ; from = lassoc
                        ; from∘to = refl
                        ; to∘from = refl
                        }
      ; lassoc = record { to = lassoc
                        ; from = rassoc
                        ; from∘to = refl
                        ; to∘from = refl
                        }
      }

instance
  ≃-BraidedCat : BraidedCat _≃_
  ≃-BraidedCat = record
    { swap = record { to = swap
                    ; from = swap
                    ; from∘to = refl
                    ; to∘from = refl
                    }
    }


-- Can I define _≣_ as a category? Try:
-- 
-- instance
--   ≡-Category  : Category _≡_
--   ≡-Category = record { id = refl
--                       ; _∘_ = trans
--                       ; id-l = {!!}
--                       ; id-r = {!!}
--                       ; assoc = {!!}
--                       }
--
-- Result:
-- 
--     A != C of type Set
--     when checking that the expression trans has type
--     B ≡ C → A ≡ B → A ≡ C
--
-- I think the issue here is that ≣ relates values (elements of types of kind
-- Set), but Category assumes domain & codomain of being types rather than
-- values. Can I simply abstract Set out of Category?
