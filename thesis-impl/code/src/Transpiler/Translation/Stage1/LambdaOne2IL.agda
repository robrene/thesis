module Transpiler.Translation.Stage1.LambdaOne2IL where

open import LambdaOne.LambdaOne

open import Transpiler.IntermediateLang.Gates.BoolTrio
open import Transpiler.IntermediateLang.IntermediateLang
open import Transpiler.IntermediateLang.Plugs
open import Transpiler.Util.PolyTypeTranslation

open import Transpiler.Translation.Stage1.CombinatorCircuits
open import Transpiler.Translation.Stage1.EitherBranchingCircuit renaming (circuit to branching-circuit)
open import Transpiler.Translation.Stage1.Padding
open import Transpiler.Translation.Stage1.Reduce

translate : ∀ {Γ Δ τ} → Λ₁ Γ Δ τ → IL[ ΛBoolTrio ] Γ (sz-list Δ) (sz τ)
translate ⟨ g ⟩                              = G⟨ g ⟩
translate #[ r ]                             = Var r
translate (f $₁ x)                           = (translate x ∥ PlugId') ⟫ translate f
translate (letₓ x inₑ e)                     = (translate x ∥ PlugId') ⟫ reduce-ctxt (translate e)
translate (x ,₁ y)                           = translate x ∥ translate y
translate (case⊗ xy of f)                    = (translate xy ∥ PlugId') ⟫ reduce-ctxt-twice (translate f)
translate (inl₁ {_} {α} {β} x)               = G⟨ FALSE ⟩ ∥ left-pad (sz α) (sz β) (translate x)
translate (inr₁ {_} {α} {β} y)               = G⟨ TRUE ⟩ ∥ right-pad (sz α) (sz β) (translate y)
translate (case⊕_either_or_ {α = α} xy f g)  = branching-circuit {a = sz α} (translate xy) (reduce-ctxt (translate f)) (reduce-ctxt (translate g))
