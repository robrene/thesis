module Data.PolyTypes.Maybe where

open import Data.PolyTypes public

open import Function using (_∘_)
open import Data.PolyTypes.Bool
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)


Maybe : Uₚ → Set
Maybe A = Tₚ (𝟙 ⊕ A)

pattern nothing = inj₁ ⊤.tt
pattern just x  = inj₂ x

is-just : ∀ {A : Uₚ} → Maybe A → Bool
is-just (just _) = true
is-just nothing  = false

is-nothing : ∀ {A : Uₚ} → Maybe A → Bool
is-nothing = not ∘ is-just

maybe : ∀ {A : Uₚ} {B : Maybe A → Uₚ} →
        ((x : Tₚ A) → Tₚ (B (just x))) → Tₚ (B nothing) → (x : Maybe A) → Tₚ (B x)
maybe j n (just x) = j x
maybe j n nothing  = n

maybe′ : ∀ {A : Uₚ} {B : Uₚ} → (Tₚ A → Tₚ B) → Tₚ B → Maybe A → Tₚ B
maybe′ = maybe
