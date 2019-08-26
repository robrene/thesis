module Transpiler.Translation.Stage2.IL2PiWare where

open import Data.List using ([])
open import Data.Nat

open import PiWare.Circuit using (ℂ[_])
open ℂ[_]

open import Transpiler.IntermediateLang.Gates.BoolTrio
open import Transpiler.IntermediateLang.IntermediateLang
open import Transpiler.IntermediateLang.Plugs using (⇇-nil)

grnd-circuit : ∀ {o} → ℂ[ ΛBoolTrio ] 0 o
grnd-circuit {zero}  = Plug (⇇-nil zero)
grnd-circuit {suc o} = Gate FALSE ∥ grnd-circuit

translate : ∀ {i o} → IL[ ΛBoolTrio ] [] i o → ℂ[ ΛBoolTrio ] i o
translate G⟨ g# ⟩   = Gate g#
translate Grnd      = grnd-circuit
translate (Plug x)  = Plug x
translate (x ⟫ y)   = translate x ⟫ translate y
translate (x ∥ y)   = translate x ∥ translate y
translate (Var ())
