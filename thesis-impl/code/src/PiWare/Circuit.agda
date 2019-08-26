module PiWare.Circuit where

open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec)
open import Data.Vec.Extras using (_⇇_)

open import PiWare.Gates

data ℂ[_] (G : Gates) : ℕ → ℕ → Set where
  Gate  : ∀ g#                                            → ℂ[ G ] (#in G g#) (#out G g#)
  Plug  : ∀ {i o}          → i ⇇ o                        → ℂ[ G ] i o
  _⟫_   : ∀ {i m o}        → ℂ[ G ] i m → ℂ[ G ] m o      → ℂ[ G ] i o
  _∥_   : ∀ {i₁ o₁ i₂ o₂}  → ℂ[ G ] i₁ o₁ → ℂ[ G ] i₂ o₂  → ℂ[ G ] (i₁ + i₂) (o₁ + o₂)

module WithGates (G : Gates) where
  ℂ : ℕ → ℕ → Set
  ℂ = ℂ[ G ]
