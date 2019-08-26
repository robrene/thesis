module Transpiler.IntermediateLang.Semantics where

open import Function using (_$_; const)
open import Data.PolyTypes.Bool
open import Data.Vec using (replicate)

open import Transpiler.Util.AtomTranslation using (⤋)

open import Transpiler.IntermediateLang.Environment
open import Transpiler.IntermediateLang.IntermediateLang

open import PiWare.Simulation (Bool) using (W; W→W; Gateσ; plugσ; seqσ; parσ) public

eval[_] : ∀ {G Γ i o} → Gateσ G → IL[ G ] Γ i o → Env Γ → W→W i o
eval[ gσ ] G⟨ g# ⟩  env = gσ g#
eval[ gσ ] Grnd     env = const (replicate false)
eval[ gσ ] (Plug x) env = plugσ x
eval[ gσ ] (x ⟫ y)  env = seqσ (eval[ gσ ] x env) (eval[ gσ ] y env)
eval[ gσ ] (x ∥ y)  env = parσ (eval[ gσ ] x env) (eval[ gσ ] y env)
eval[ gσ ] (Var x)  env = const $ ⤋ (env ! x)
