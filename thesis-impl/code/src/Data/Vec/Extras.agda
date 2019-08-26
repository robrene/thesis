module Data.Vec.Extras where

open import Function using (_$_)
open import Data.Fin using (Fin)
open import Data.Nat
open import Data.Nat.Extras
open import Data.Nat.Properties using (+-suc)
open import Data.Product
open import Data.Vec hiding (take; drop)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

coerce-vec : ∀ {a} {A : Set a} {m n} → m ≡ n → Vec A m → Vec A n
coerce-vec refl v = v

_⇇_ : ℕ → ℕ → Set
i ⇇ o = Vec (Fin i) o

take : ∀ {a} {A : Set a} m {n} → Vec A (m + n) → Vec A m
take zero v = []
take (suc m) (x ∷ v) = x ∷ take m v

drop : ∀ {a} {A : Set a} m {n} → Vec A (m + n) → Vec A n
drop zero v = v
drop (suc m) (x ∷ v) = drop m v

split|n+n| : ∀ {a} {A : Set a} {n : ℕ} → Vec A (n + n) → Vec A n × Vec A n
split|n+n| {n = zero}        []            = [] , []
split|n+n| {n = suc zero}    (x ∷ y ∷ [])  = x ∷ [] , y ∷ []
split|n+n| {n = suc (suc n)} (x ∷ y ∷ v)   with split|n+n| {n = suc n} (coerce-vec (+-suc n (suc n)) v)
... | vs₁ , vs₂ = x ∷ vs₁ , y ∷ vs₂

intersperse-vecs : ∀ {a} {A : Set a} {n : ℕ} → Vec A n → Vec A n → Vec A (n ·2)
intersperse-vecs [] [] = []
intersperse-vecs (x ∷ v) (y ∷ w) = x ∷ y ∷ intersperse-vecs v w
