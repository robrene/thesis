module Transpiler.Translation.Properties.Correctness where

open import Data.List using ([])
open import Data.PolyTypes.Bool
open import Relation.Binary.PropositionalEquality

open import LambdaOne.Environment using (ε)
open import LambdaOne.LambdaOne using (Λ₁)
open import LambdaOne.Unembedding using (unembed)
open import PiWare.Circuit using (ℂ[_])
open import PiWare.Simulation (Bool) using (⟦_⟧[_])

open import Transpiler.IntermediateLang.Semantics using (eval[_])
open import Transpiler.IntermediateLang.Semantics.BoolTrio using (ΛBoolTrioσ)
open import Transpiler.Util.AtomTranslation using (atomize)

open import Transpiler.Translation.Stage1.LambdaOne2IL using () renaming (translate to Λ₁⟶IL)
open import Transpiler.Translation.Stage2.IL2PiWare using () renaming (translate to IL⟶ΠW)
open import Transpiler.Translation.Translation using (translate)

-- Intermediate proofs:
open import Transpiler.Translation.Stage1.Properties.Correctness using () renaming (translate-correctness to stage1-correctness)
open import Transpiler.Translation.Stage2.Properties.Correctness using () renaming (translate-correctness to stage2-correctness)

translate-correctness : ∀ {Δ τ} → (e : Λ₁ [] Δ τ) → ⟦ translate e ⟧[ ΛBoolTrioσ ] ≡ atomize {Δ} (unembed e ε)
translate-correctness {Δ} e = let open ≡-Reasoning in ≡-Reasoning.begin
    ⟦ translate e ⟧[ ΛBoolTrioσ ]
  ≡⟨ refl ⟩
    ⟦ IL⟶ΠW (Λ₁⟶IL e) ⟧[ ΛBoolTrioσ ]
  ≡⟨ stage2-correctness (Λ₁⟶IL e) ⟩
    eval[ ΛBoolTrioσ ] (Λ₁⟶IL e) ε
  ≡⟨ stage1-correctness e ⟩
    atomize {Δ} (unembed e ε)
  ∎
