module LambdaOne.Unembedding where

open import Function using (_$_)
open import Data.List using (List; _∷_) renaming ([] to ε)
open import Data.PolyTypes.Bool
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)

open import LambdaOne.Environment
open import LambdaOne.LambdaOne

infixr 4 _⇀_ _↣_

data ΛSet : Set where
  _⊩   : (τ : Uₚ) → ΛSet
  _⇀_  : (σ : Uₚ) → (A : ΛSet) → ΛSet

open ΛSet public

_↣_ : (Δ : List Uₚ) → (τ : Uₚ) → ΛSet
ε       ↣ τ = τ ⊩
(x ∷ Δ) ↣ τ = x ⇀ (Δ ↣ τ)

Λ⟦_⟧ : ΛSet → Set
Λ⟦ τ ⊩    ⟧  = Tₚ τ
Λ⟦ σ ⇀ τs ⟧  = Tₚ σ → Λ⟦ τs ⟧

GateTy : (g : Gate) → ΛSet
GateTy g = inputs g ↣ output g

unembed-gate : (g : Gate) → Λ⟦ GateTy g ⟧
unembed-gate TRUE   = true
unembed-gate FALSE  = false
unembed-gate NOT    = not
unembed-gate AND    = _∧_
unembed-gate OR     = _∨_

-- Unembedding for LambdaOne, using an environment to give values to bindings:
unembed : ∀ {Γ Δ τ} → (x : Λ₁ Γ Δ τ) → Env Γ → Λ⟦ Δ ↣ τ ⟧
unembed ⟨ g ⟩                     env  = unembed-gate g
unembed #[ r ]                    env  = env ! r
unembed (f $₁ x)                  env  = (unembed f env) (unembed x env)
unembed (letₓ x inₑ e)            env  = unembed e ((unembed x env) ∷ env)
unembed (x ,₁ y)                  env  = (unembed x env) , (unembed y env)
unembed (case⊗ xy of f)           env  = unembed f ((proj₁ $ unembed xy env) ∷ (proj₂ $ unembed xy env) ∷ env)
unembed (inl₁ x)                  env  = inj₁ (unembed x env)
unembed (inr₁ y)                  env  = inj₂ (unembed y env)
unembed (case⊕ xy either f or g)  env  with unembed xy env
... | inj₁ x                           = unembed f (x ∷ env)
... | inj₂ y                           = unembed g (y ∷ env)
