module Transpiler.IntermediateLang.Gates.BoolTrio where

open import Function using (_∘_)

open import LambdaOne.LambdaOne using (Gate; inputs; output)
open Gate public

open import Transpiler.Util.PolyTypeTranslation using (sz; sz-list)

open import Transpiler.IntermediateLang.Gates public

ΛBoolTrio : Gates
ΛBoolTrio = record { Gate#  = Gate
                   ; #in    = sz-list ∘ inputs
                   ; #out   = sz ∘ output
                   }
