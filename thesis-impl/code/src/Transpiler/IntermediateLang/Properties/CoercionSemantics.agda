module Transpiler.IntermediateLang.Properties.CoercionSemantics where

open import Function using (_$_)
open import Data.Vec.Extras
open import Relation.Binary.PropositionalEquality

open import Transpiler.IntermediateLang.Coerce
open import Transpiler.IntermediateLang.Environment
open import Transpiler.IntermediateLang.IntermediateLang
open import Transpiler.IntermediateLang.Semantics

coerceᵢₒ-semantics-lemma : ∀ {G Γ i i' o o'} {gσ : Gateσ G} {env : Env Γ} {w : W i'} →
                           (i≡ : i ≡ i') → (o≡ : o ≡ o') →
                           (e : IL[ G ] Γ i o) →
                           eval[ gσ ] (coerceᵢₒ i≡ o≡ e) env w ≡ (coerce-vec o≡ $ (eval[ gσ ] e env) (coerce-vec (sym i≡) w))
coerceᵢₒ-semantics-lemma {i = i} {i' = .i} {o = o} {o' = .o} refl refl e = refl

coerceᵢ-semantics-lemma : ∀ {G Γ i i' o} {gσ : Gateσ G} {env : Env Γ} {w : W i'} →
                          (i≡ : i ≡ i') →
                          (e : IL[ G ] Γ i o) →
                          eval[ gσ ] (coerceᵢ i≡ e) env w ≡ (eval[ gσ ] e env) (coerce-vec (sym i≡) w)
coerceᵢ-semantics-lemma {i = i} {i' = .i} refl e = refl

coerceₒ-semantics-lemma : ∀ {G Γ i o o'} {gσ : Gateσ G} {env : Env Γ} {w : W i} →
                          (o≡ : o ≡ o') →
                          (e : IL[ G ] Γ i o) →
                          eval[ gσ ] (coerceₒ o≡ e) env w ≡ (coerce-vec o≡ $ (eval[ gσ ] e env) w)
coerceₒ-semantics-lemma {o = o} {o' = .o} refl e = refl
