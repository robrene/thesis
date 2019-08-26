module Transpiler.Translation.Stage1.Reduce where

open import Function using (_$_)
open import Data.List using (_∷_)
open import Data.Nat using (_+_)
open import Data.Nat.Properties using (+-assoc; +-right-identity)
open import Relation.Binary.PropositionalEquality using (sym)

open import Transpiler.IntermediateLang.Coerce
open import Transpiler.IntermediateLang.Environment
open import Transpiler.IntermediateLang.IntermediateLang
open import Transpiler.IntermediateLang.Plugs
open import Transpiler.Util.PolyTypeTranslation using (sz)

open import Transpiler.Translation.Stage1.CombinatorCircuits

-- Reduce the context by one element by adding it as an additional input of
-- the circuit
reduce-ctxt : ∀ {G τ Γ i o} → IL[ G ] (τ ∷ Γ) i o → IL[ G ] Γ (sz τ + i) o
reduce-ctxt {_} {τ} G⟨ g# ⟩        = K[ sz τ ]· G⟨ g# ⟩
reduce-ctxt {_} {τ} Grnd           = K[ sz τ ]· Grnd
reduce-ctxt {_} {τ} (Plug x)       = K[ sz τ ]· Plug x
reduce-ctxt {_} {τ} (x ⟫ y)        = S[ sz τ ]· reduce-ctxt x · reduce-ctxt y
reduce-ctxt {_} {τ} (x ∥ y)        = P[ sz τ ]· reduce-ctxt x · reduce-ctxt y
reduce-ctxt {_} {τ} (Var top)      = coerceᵢ (sym $ +-right-identity (sz τ)) $ PlugId (sz τ)
reduce-ctxt {_} {τ} (Var (pop i))  = K[ sz τ ]· Var i

-- Reduce the context by two elements by adding them as additional inputs of
-- the circuit
reduce-ctxt-twice : ∀ {G α β Γ i o} → IL[ G ] (α ∷ β ∷ Γ) i o → IL[ G ] Γ (sz α + sz β + i) o
reduce-ctxt-twice {G} {α} {β} {Γ} {i} f = PlugReorderArgs ⟫ reduce-ctxt (reduce-ctxt f)
  where
    PlugReorderArgs : IL[ G ] Γ (sz α + sz β + i) (sz β + (sz α + i))
    PlugReorderArgs = coerceₒ (+-assoc (sz β) (sz α) i) $ PlugFlip (sz α) (sz β) ∥ PlugId i
