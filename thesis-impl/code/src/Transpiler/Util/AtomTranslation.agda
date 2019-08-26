module Transpiler.Util.AtomTranslation where

open import Function using (_$_)
open import Data.List using ([]; _∷_)
open import Data.PolyTypes.Bool
open import Data.Product using (_,_)
open import Data.Nat using (suc; _+_)
open import Data.Nat.Extras using (_⊔₂_; compare₂; lesseq; greater)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Vec using ([]; _∷_; _++_; replicate)
open import Data.Vec.Extras using (take; drop)
open import Relation.Binary.PropositionalEquality using (sym)

open import LambdaOne.Unembedding using (Λ⟦_⟧; _↣_)
open import PiWare.Simulation (Bool) using (W; W→W)

open import Transpiler.Util.PolyTypeTranslation

pad₁ : ∀ {m} n → W m → W (m ⊔₂ n)
pad₁ {m} n w with compare₂ m n
pad₁ {.m}           .(m + k) w | lesseq m k  = w ++ replicate false
pad₁ {.(m + suc k)} .m       w | greater m k = w

pad₂ : ∀ m {n} → W n → W (m ⊔₂ n)
pad₂ m {n} w with compare₂ m n
pad₂ .m           {.(m + k)} w | lesseq m k  = w
pad₂ .(m + suc k) {.m}       w | greater m k = w ++ replicate false

⤋ : ∀ {τ} → Tₚ τ → W (sz τ)
⤋ {𝟙}     _        = []
⤋ {σ ⊗ τ} (x , y)  = ⤋ x ++ ⤋ y
⤋ {σ ⊕ τ} (inj₁ x) = false ∷ pad₁ (sz τ) (⤋ x)
⤋ {σ ⊕ τ} (inj₂ y) = true ∷ pad₂ (sz σ) (⤋ y)

unpad₁ : ∀ m n → W (m ⊔₂ n) → W m
unpad₁ m n w with compare₂ m n
unpad₁ .m           .(m + k) w | lesseq m k  = take m w
unpad₁ .(m + suc k) .m       w | greater m k = w

unpad₂ : ∀ m n → W (m ⊔₂ n) → W n
unpad₂ m n w with compare₂ m n
unpad₂ .m           .(m + k) w | lesseq m k  = w
unpad₂ .(m + suc k) .m       w | greater m k = take m w

⤊ : ∀ {τ} → W (sz τ) → Tₚ τ
⤊ {𝟙}     _           = ⊤.tt
⤊ {σ ⊗ τ} w           = ⤊ (take (sz σ) w) , ⤊ (drop (sz σ) w)
⤊ {σ ⊕ τ} (false ∷ w) = inj₁ (⤊ (unpad₁ (sz σ) (sz τ) w))
⤊ {σ ⊕ τ} (true ∷ w)  = inj₂ (⤊ (unpad₂ (sz σ) (sz τ) w))

atomize : ∀ {Δ τ} → Λ⟦ Δ ↣ τ ⟧ → W→W (sz-list Δ) (sz τ)
atomize {[]}    l  = Function.const $ ⤋ l
atomize {σ ∷ Δ} l  = λ i → atomize {Δ} (l $ ⤊ {σ} (take (sz σ) i)) (drop (sz σ) i)
