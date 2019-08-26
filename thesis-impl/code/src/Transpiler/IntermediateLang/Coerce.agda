module Transpiler.IntermediateLang.Coerce where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Transpiler.IntermediateLang.IntermediateLang using (IL[_])

coerceᵢₒ : ∀ {G Γ i i' o o'} → i ≡ i' → o ≡ o' → IL[ G ] Γ i o → IL[ G ] Γ i' o'
coerceᵢₒ refl refl e = e

coerceᵢ : ∀ {G Γ i i' o} → i ≡ i' → IL[ G ] Γ i o → IL[ G ] Γ i' o
coerceᵢ refl e = e

coerceₒ : ∀ {G Γ i o o'} → o ≡ o' → IL[ G ] Γ i o → IL[ G ] Γ i o'
coerceₒ refl e = e
