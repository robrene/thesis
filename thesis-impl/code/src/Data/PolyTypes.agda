module Data.PolyTypes where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)

data Uₚ : Set where
  𝟙    : Uₚ
  _⊗_  : Uₚ → Uₚ → Uₚ
  _⊕_  : Uₚ → Uₚ → Uₚ

open Uₚ public

infixr 1 _⊕_
infixr 2 _⊗_

𝟚 : Uₚ
𝟚 = 𝟙 ⊕ 𝟙

Tₚ : Uₚ → Set
Tₚ 𝟙        = ⊤
Tₚ (σ ⊗ τ)  = Tₚ σ × Tₚ τ
Tₚ (σ ⊕ τ)  = Tₚ σ ⊎ Tₚ τ
