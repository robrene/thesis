module Transpiler.Util.AtomTranslation.Properties where

open import Data.Nat using (suc; _+_)
open import Data.Nat.Extras using (compare₂; lesseq; greater)
open import Data.PolyTypes.Bool
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (_++_)
open import Data.Vec.Extras using (take; drop)
open import Data.Vec.Properties.Extras using (take-++-identity; drop-++-identity)
open import Relation.Binary.PropositionalEquality

open import PiWare.Simulation (Bool) using (W)

open import Transpiler.Util.AtomTranslation
open import Transpiler.Util.PolyTypeTranslation

unpad₁∘pad₁-identity : ∀ {m} n {w : W m} → unpad₁ m n (pad₁ n w) ≡ w
unpad₁∘pad₁-identity {m} n with compare₂ m n
unpad₁∘pad₁-identity {.m}           .(m + k) | lesseq m k  = take-++-identity
unpad₁∘pad₁-identity {.(m + suc k)} .m       | greater m k = refl

unpad₂∘pad₂-identity : ∀ m {n} {w : W n} → unpad₂ m n (pad₂ m w) ≡ w
unpad₂∘pad₂-identity m {n} {w} with compare₂ m n
unpad₂∘pad₂-identity .m           {.(m + k)} | lesseq m k  = refl
unpad₂∘pad₂-identity .(m + suc k) {.m}       | greater m k = take-++-identity

⤊∘⤋-identity : ∀ {τ} (x : Tₚ τ) → ⤊ (⤋ x) ≡ x
⤊∘⤋-identity {𝟙}     _ = refl
⤊∘⤋-identity {σ ⊗ τ} (x , y) = let open ≡-Reasoning in ≡-Reasoning.begin
    ⤊ (take (sz σ) (⤋ x ++ ⤋ y)) , ⤊ (drop (sz σ) (⤋ x ++ ⤋ y))
  ≡⟨ cong₂ (λ p q → ⤊ p , ⤊ q) take-++-identity (drop-++-identity (⤋ x)) ⟩
    ⤊ (⤋ x) ,  ⤊ (⤋ y)
  ≡⟨ cong₂ (λ p q → p , q) (⤊∘⤋-identity x) (⤊∘⤋-identity y) ⟩
    x , y
  ∎
⤊∘⤋-identity {σ ⊕ τ} (inj₁ x) = let open ≡-Reasoning in ≡-Reasoning.begin
    inj₁ (⤊ (unpad₁ (sz σ) (sz τ) (pad₁ (sz τ) (⤋ x))))
  ≡⟨ cong (λ z → inj₁ (⤊ z)) (unpad₁∘pad₁-identity (sz τ)) ⟩
    inj₁ (⤊ (⤋ x))
  ≡⟨ cong inj₁ (⤊∘⤋-identity x) ⟩
    inj₁ x
  ∎
⤊∘⤋-identity {σ ⊕ τ} (inj₂ y) = let open ≡-Reasoning in ≡-Reasoning.begin
    inj₂ (⤊ (unpad₂ (sz σ) (sz τ) (pad₂ (sz σ) (⤋ y))))
  ≡⟨ cong (λ z → inj₂ (⤊ z)) (unpad₂∘pad₂-identity (sz σ)) ⟩
    inj₂ (⤊ (⤋ y))
  ≡⟨ cong inj₂ (⤊∘⤋-identity y) ⟩
    inj₂ y
  ∎
