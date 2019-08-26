module Relation.Binary.PropositionalEquality.Extras where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core using (Symmetric; Rel)

sym-sym-relation : ∀ {a} {A : Set a} {i : A} {j : A} → (R : i ≡ j) → sym (sym R) ≡ R
sym-sym-relation refl = refl
