module Data.Vec.Properties.Coercion where

open import Function using (_$_)
open import Data.Nat using (_+_; zero; suc)
open import Data.Nat.Properties using (suc-injective; +-assoc)
open import Data.Vec using (Vec; []; _∷_; _++_)
open import Data.Vec.Extras using (coerce-vec; take; drop)
open import Data.Vec.Properties.Extras using (take-++-identity; drop-++-identity)
open import Data.Vec.Relation.Equality.Propositional using (≋⇒≡)
open import Relation.Binary.PropositionalEquality

import Data.Vec.Relation.Equality.Setoid as SEq

coerce-vec-cong-suc-lemma : ∀ {a} {A : Set a} {m n} →
                            (m≡n : m ≡ n) →
                            (x : A) →
                            (vₘ : Vec A m) →
                            (coerce-vec (cong suc m≡n) (x ∷ vₘ)) ≡ x ∷ (coerce-vec m≡n vₘ)
coerce-vec-cong-suc-lemma refl x vₘ = refl

take-++-identity-c+a : ∀ {a} {A : Set a} {m k₀ k₁} →
                       (vₘ : Vec A m) → (v₀ : Vec A k₀) → (v₁ : Vec A k₁) →
                       take m (coerce-vec (+-assoc m k₀ k₁) ((vₘ ++ v₀) ++ v₁)) ≡ vₘ
take-++-identity-c+a {m = zero} {k₀} {k₁} [] v₀ v₁ = refl
take-++-identity-c+a {m = suc m} {k₀} {k₁} (x ∷ vₘ) v₀ v₁ =
  let open ≡-Reasoning in ≡-Reasoning.begin
    take (suc m) (coerce-vec (cong suc (+-assoc m k₀ k₁)) (x ∷ ((vₘ ++ v₀) ++ v₁)))
  ≡⟨ cong (take (suc m)) (coerce-vec-cong-suc-lemma (+-assoc m k₀ k₁) x ((vₘ ++ v₀) ++ v₁)) ⟩
    x ∷ take m (coerce-vec (+-assoc m k₀ k₁) ((vₘ ++ v₀) ++ v₁))
  ≡⟨ cong (λ z → x ∷ z) (take-++-identity-c+a vₘ v₀ v₁) ⟩
    x ∷ vₘ
  ∎

drop-++-identity-c+a : ∀ {a} {A : Set a} {m k₀ k₁} →
                       (vₘ : Vec A m) → (v₀ : Vec A k₀) → (v₁ : Vec A k₁) →
                       drop m (coerce-vec (+-assoc m k₀ k₁) ((vₘ ++ v₀) ++ v₁)) ≡ v₀ ++ v₁
drop-++-identity-c+a {m = zero} {k₀} {k₁} [] v₀ v₁ = refl
drop-++-identity-c+a {m = suc m} {k₀} {k₁} (x ∷ vₘ) v₀ v₁ =
  let open ≡-Reasoning in ≡-Reasoning.begin
    drop (suc m) (coerce-vec (cong suc (+-assoc m k₀ k₁)) (x ∷ ((vₘ ++ v₀) ++ v₁)))
  ≡⟨ cong (drop (suc m)) (coerce-vec-cong-suc-lemma (+-assoc m k₀ k₁) x ((vₘ ++ v₀) ++ v₁)) ⟩
    drop m (coerce-vec (+-assoc m k₀ k₁) ((vₘ ++ v₀) ++ v₁))
  ≡⟨ drop-++-identity-c+a vₘ v₀ v₁ ⟩
    v₀ ++ v₁
  ∎

coerce-vec-sym-cong-suc-lemma : ∀ {a} {A : Set a} {m n} →
                              (m≡n : m ≡ n) →
                              (x : A) →
                              (vₙ : Vec A n) →
                              (coerce-vec (sym $ cong suc m≡n) (x ∷ vₙ)) ≡ x ∷ (coerce-vec (sym m≡n) vₙ)
coerce-vec-sym-cong-suc-lemma refl x vₙ = refl

take-++-identity-c+sa : ∀ {a} {A : Set a} {m k₀ k₁} →
                        (vₘ : Vec A m) → (v₀₁ : Vec A (k₀ + k₁)) →
                        take (m + k₀) (coerce-vec (sym $ +-assoc m k₀ k₁) (vₘ ++ v₀₁)) ≡ vₘ ++ take k₀ v₀₁
take-++-identity-c+sa {m = zero} {_} {_} [] v₀₁ = refl
take-++-identity-c+sa {m = suc m} {k₀} {k₁} (x ∷ vₘ) v₀₁ =
  let open ≡-Reasoning in ≡-Reasoning.begin
    take (suc (m + k₀)) (coerce-vec (sym $ cong suc (+-assoc m k₀ k₁)) (x ∷ vₘ ++ v₀₁))
  ≡⟨ cong (take (suc (m + k₀))) (coerce-vec-sym-cong-suc-lemma (+-assoc m k₀ k₁) x (vₘ ++ v₀₁)) ⟩
    x ∷ (take (m + k₀) (coerce-vec (sym $ +-assoc m k₀ k₁) (vₘ ++ v₀₁)))
  ≡⟨ cong (λ z → x ∷ z) (take-++-identity-c+sa vₘ v₀₁) ⟩
    x ∷ vₘ ++ take k₀ v₀₁
  ∎

drop-++-identity-c+sa : ∀ {a} {A : Set a} {m k₀ k₁} →
                        (vₘ : Vec A m) → (v₀₁ : Vec A (k₀ + k₁)) →
                        drop (m + k₀) (coerce-vec (sym $ +-assoc m k₀ k₁) (vₘ ++ v₀₁)) ≡ drop k₀ v₀₁
drop-++-identity-c+sa {m = zero} {_} {_} [] v₀₁ = refl
drop-++-identity-c+sa {m = suc m} {k₀} {k₁} (x ∷ vₘ) v₀₁ =
  let open ≡-Reasoning in ≡-Reasoning.begin
    drop (suc (m + k₀)) (coerce-vec (sym $ cong suc (+-assoc m k₀ k₁)) (x ∷ vₘ ++ v₀₁))
  ≡⟨ cong (drop (suc (m + k₀))) (coerce-vec-sym-cong-suc-lemma (+-assoc m k₀ k₁) x (vₘ ++ v₀₁)) ⟩
    drop (m + k₀) (coerce-vec (sym $ +-assoc m k₀ k₁) (vₘ ++ v₀₁))
  ≡⟨ drop-++-identity-c+sa vₘ v₀₁ ⟩
    drop k₀ v₀₁
  ∎

uncoerce-vec-++-[] : ∀ {a} {A : Set a} {n} →
                     (p : n + 0 ≡ n) → (v : Vec A n) →
                     coerce-vec p (v ++ []) ≡ v
uncoerce-vec-++-[] {n = zero} refl [] = refl
uncoerce-vec-++-[] {n = suc n} p (x ∷ v₀) = trans (cons-coerce-lemma p x (v₀ ++ [])) (cong (_∷_ x) (uncoerce-vec-++-[] (suc-injective p) v₀))
  where cons-coerce-lemma : ∀ {a} {A : Set a} {m n} →
                            (p : suc m ≡ suc n) → (x : A) → (v : Vec A m) →
                            coerce-vec p (x ∷ v) ≡ x ∷ coerce-vec (suc-injective p) v
        cons-coerce-lemma refl x v = refl
