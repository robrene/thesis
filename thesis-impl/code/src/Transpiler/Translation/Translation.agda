module Transpiler.Translation.Translation where

open import Function using (_∘_)
open import Data.List using ([])

open import LambdaOne.LambdaOne using (Λ₁)
open import PiWare.Circuit using (ℂ[_])
open import Transpiler.IntermediateLang.Gates.BoolTrio using (ΛBoolTrio)
open import Transpiler.Util.PolyTypeTranslation using (sz; sz-list)

open import Transpiler.Translation.Stage1.LambdaOne2IL renaming (translate to Λ₁⟶IL)
open import Transpiler.Translation.Stage2.IL2PiWare renaming (translate to IL⟶ΠW)

translate : ∀ {Δ τ} → (e : Λ₁ [] Δ τ) → ℂ[ ΛBoolTrio ] (sz-list Δ) (sz τ)
translate = IL⟶ΠW ∘ Λ₁⟶IL
