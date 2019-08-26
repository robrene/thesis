module Transpiler.Util.PolyTypeTranslation where

open import Function using (_∘_)
open import Data.List using (List; map; sum)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Extras using (_⊔₂_)
open import Data.PolyTypes

sz : (τ : Uₚ) → ℕ
sz 𝟙         = zero
sz (τ₁ ⊗ τ₂) = sz τ₁ + sz τ₂
sz (τ₁ ⊕ τ₂) = suc (sz τ₁ ⊔₂ sz τ₂)

sz-list : List Uₚ → ℕ
sz-list = sum ∘ map sz
