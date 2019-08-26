module Transpiler.IntermediateLang.Semantics.BoolTrio where

open import Data.PolyTypes.Bool
open import Data.Vec using ([]; _∷_; [_])

open import LambdaOne.LambdaOne using (Gate)
open Gate
open import Transpiler.IntermediateLang.Gates.BoolTrio using (ΛBoolTrio)
open import Transpiler.IntermediateLang.Semantics using (Gateσ)

ΛBoolTrioσ : Gateσ ΛBoolTrio
ΛBoolTrioσ TRUE  []           = [ true ]
ΛBoolTrioσ FALSE []           = [ false ]
ΛBoolTrioσ NOT   (x ∷ [])     = [ not x ]
ΛBoolTrioσ AND   (x ∷ y ∷ []) = [ x ∧ y ]
ΛBoolTrioσ OR    (x ∷ y ∷ []) = [ x ∨ y ]
