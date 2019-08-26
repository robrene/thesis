module PiWare.Simulation (Atom : Set) where

open import Function using (_∘_; flip)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; _++_; lookup; tabulate)
open import Data.Vec.Extras using (_⇇_; take; drop)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PiWare.Circuit
open import PiWare.Gates

-- Variable-size word:
W : ℕ → Set
W = Vec Atom

W→W : ℕ → ℕ → Set
W→W i o = W i → W o

-- Type for evaluation semantics of Gates:
Gateσ : (G : Gates) → Set
Gateσ G = ∀ g# → W→W (#in G g#) (#out G g#)

-- Evaluation semantics of Plug:
plugσ : ∀ {i o} → i ⇇ o → W→W i o
plugσ p w = tabulate (flip lookup w ∘ flip lookup p)
-- Evaluation semantics of _⟫_:
seqσ : ∀ {i m o} → W→W i m → W→W m o → W→W i o
seqσ f₁ f₂ = f₂ ∘ f₁
-- Evaluation semantics of _∥_:
parσ : ∀ {i₁ o₁ i₂ o₂} → W→W i₁ o₁ → W→W i₂ o₂ → W→W (i₁ + i₂) (o₁ + o₂)
parσ {i₁} f₁ f₂ w = f₁ (take i₁ w) ++ f₂ (drop i₁ w)

-- Evaluation semantics for PiWare:
⟦_⟧[_] : ∀ {G i o} → ℂ[ G ] i o → Gateσ G → W→W i o
⟦ Gate g#  ⟧[ gσ ] = gσ g#
⟦ Plug x   ⟧[ gσ ] = plugσ x
⟦ c₁ ⟫ c₂  ⟧[ gσ ] = seqσ ⟦ c₁ ⟧[ gσ ] ⟦ c₂ ⟧[ gσ ]
⟦ c₁ ∥ c₂  ⟧[ gσ ] = parσ ⟦ c₁ ⟧[ gσ ] ⟦ c₂ ⟧[ gσ ]
