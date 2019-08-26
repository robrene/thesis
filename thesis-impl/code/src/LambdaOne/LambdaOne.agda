module LambdaOne.LambdaOne where

open import Data.List using (List; []; _∷_)
open import Data.PolyTypes

open import LambdaOne.Environment

data Gate : Set where
  TRUE FALSE NOT AND OR : Gate

open Gate public

inputs : Gate → List Uₚ
inputs TRUE   = []
inputs FALSE  = []
inputs NOT    = 𝟚 ∷ []
inputs AND    = 𝟚 ∷ 𝟚 ∷ []
inputs OR     = 𝟚 ∷ 𝟚 ∷ []

output : Gate → Uₚ
output TRUE   = 𝟚
output FALSE  = 𝟚
output NOT    = 𝟚
output AND    = 𝟚
output OR     = 𝟚

data Λ₁ : (Γ : Ctxt) → (Δ : List Uₚ) → (τ : Uₚ) → Set where
  ⟨_⟩               : ∀ {Γ}          → (g : Gate)                                                            → Λ₁ Γ (inputs g) (output g)
  #[_]              : ∀ {Γ τ}        → (r : Ref Γ τ)                                                         → Λ₁ Γ [] τ
  _$₁_              : ∀ {Γ Δ α β}    → (f : Λ₁ Γ (α ∷ Δ) β) → (x : Λ₁ Γ [] α)                                → Λ₁ Γ Δ β
  letₓ_inₑ_         : ∀ {Γ Δ α τ}    → (x : Λ₁ Γ [] α) → (e : Λ₁ (α ∷ Γ) Δ τ)                                → Λ₁ Γ Δ τ
  _,₁_              : ∀ {Γ α β}      → (x : Λ₁ Γ [] α) → (y : Λ₁ Γ [] β)                                     → Λ₁ Γ [] (α ⊗ β)
  case⊗_of_         : ∀ {Γ Δ α β τ}  → (xy : Λ₁ Γ [] (α ⊗ β)) → (f : Λ₁ (α ∷ β ∷ Γ) Δ τ)                     → Λ₁ Γ Δ τ
  inl₁              : ∀ {Γ α β}      → (x : Λ₁ Γ [] α)                                                       → Λ₁ Γ [] (α ⊕ β)
  inr₁              : ∀ {Γ α β}      → (y : Λ₁ Γ [] β)                                                       → Λ₁ Γ [] (α ⊕ β)
  case⊕_either_or_  : ∀ {Γ Δ α β τ}  → (xy : Λ₁ Γ [] (α ⊕ β)) → (f : Λ₁ (α ∷ Γ) Δ τ) → (g : Λ₁ (β ∷ Γ) Δ τ)  → Λ₁ Γ Δ τ

infixl 10 _$₁_

#₀ : ∀ {Γ τ₀}              → Λ₁ (τ₀ ∷ Γ) [] τ₀
#₀ = #[ top ]
#₁ : ∀ {Γ τ₀ τ₁}           → Λ₁ (τ₀ ∷ τ₁ ∷ Γ) [] τ₁
#₁ = #[ pop top ]
#₂ : ∀ {Γ τ₀ τ₁ τ₂}        → Λ₁ (τ₀ ∷ τ₁ ∷ τ₂ ∷ Γ) [] τ₂
#₂ = #[ pop (pop top) ]
#₃ : ∀ {Γ τ₀ τ₁ τ₂ τ₃}     → Λ₁ (τ₀ ∷ τ₁ ∷ τ₂ ∷ τ₃ ∷ Γ) [] τ₃
#₃ = #[ pop (pop (pop top)) ]
#₄ : ∀ {Γ τ₀ τ₁ τ₂ τ₃ τ₄}  → Λ₁ (τ₀ ∷ τ₁ ∷ τ₂ ∷ τ₃ ∷ τ₄ ∷ Γ) [] τ₄
#₄ = #[ pop (pop (pop (pop top))) ]

Λι : (Δ : List Uₚ) → (τ : Uₚ) → Set
Λι Δ τ = ∀ {Γ} → Λ₁ Γ Δ τ

⟨TRUE⟩ : Λι [] 𝟚
⟨TRUE⟩ = ⟨ TRUE ⟩

⟨FALSE⟩ : Λι [] 𝟚
⟨FALSE⟩ = ⟨ FALSE ⟩

⟨NOT⟩ : Λι (𝟚 ∷ []) 𝟚
⟨NOT⟩ = ⟨ NOT ⟩

⟨AND⟩ : Λι (𝟚 ∷ 𝟚 ∷ []) 𝟚
⟨AND⟩ = ⟨ AND ⟩

⟨OR⟩ : Λι (𝟚 ∷ 𝟚 ∷ []) 𝟚
⟨OR⟩ = ⟨ OR ⟩

fn-not : Λι [] 𝟚 → Λι [] 𝟚
fn-not x = ⟨NOT⟩ $₁ x
syntax fn-not x = ⟨not⟩ x

fn-and : Λι [] 𝟚 → Λι [] 𝟚 → Λι [] 𝟚
fn-and x y = (⟨AND⟩ $₁ x) $₁ y
syntax fn-and x y = x ⟨and⟩ y

fn-or : Λι [] 𝟚 → Λι [] 𝟚 → Λι [] 𝟚
fn-or x y = (⟨OR⟩ $₁ x) $₁ y
syntax fn-or x y = x ⟨or⟩ y

fn-nand : Λι [] 𝟚 → Λι [] 𝟚 → Λι [] 𝟚
fn-nand x y = ⟨not⟩ (x ⟨and⟩ y)
syntax fn-nand x y = x ⟨nand⟩ y

fn-xor : Λι [] 𝟚 → Λι [] 𝟚 → Λι [] 𝟚
fn-xor x y = (x ⟨or⟩ y) ⟨and⟩ (⟨not⟩ (x ⟨and⟩ y))
syntax fn-xor x y = x ⟨xor⟩ y
