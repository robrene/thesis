module Transpiler.IntermediateLang.IntermediateLang where

open import Data.Nat using (ℕ; _+_)
open import Data.Vec.Extras using (_⇇_)

open import Transpiler.Util.PolyTypeTranslation using (sz)

open import Transpiler.IntermediateLang.Gates
open import Transpiler.IntermediateLang.Environment

data IL[_] (G : Gates) : (Γ : Ctxt) → ℕ → ℕ → Set where
  G⟨_⟩  : ∀ {Γ}              → (g# : Gate# G)           → IL[ G ] Γ (#in G g#) (#out G g#)
  Grnd  : ∀ {Γ o}                                       → IL[ G ] Γ 0 o
  Plug  : ∀ {Γ i o}          → i ⇇ o                    → IL[ G ] Γ i o
  _⟫_   : ∀ {Γ i j o}        → IL[ G ] Γ i j → IL[ G ] Γ j o      → IL[ G ] Γ i o
  _∥_   : ∀ {Γ i₁ o₁ i₂ o₂}  → IL[ G ] Γ i₁ o₁ → IL[ G ] Γ i₂ o₂  → IL[ G ] Γ (i₁ + i₂) (o₁ + o₂)
  Var   : ∀ {Γ τ}            → Ref Γ τ                  → IL[ G ] Γ 0 (sz τ)

infixl 4 _⟫_
infixl 5 _∥_

open IL[_] public
