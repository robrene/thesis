module Transpiler.Translation.Stage2.Properties.Correctness where

open import Function using (const)
open import Data.List using ([])
open import Data.Nat
open import Data.PolyTypes.Bool
open import Data.Vec using (replicate)
open import Relation.Binary.PropositionalEquality

open import PiWare.Circuit
open import PiWare.Simulation (Bool) using (⟦_⟧[_])

open import Transpiler.IntermediateLang.Environment using (ε)
open import Transpiler.IntermediateLang.Gates.BoolTrio
open import Transpiler.IntermediateLang.IntermediateLang
open import Transpiler.IntermediateLang.Semantics
open import Transpiler.IntermediateLang.Semantics.BoolTrio using () renaming (ΛBoolTrioσ to gσ)

open import Transpiler.Translation.Stage2.IL2PiWare using (translate; grnd-circuit)

grnd-circuit-correctness : ∀ {o} → ⟦ grnd-circuit {o} ⟧[ gσ ] ≡ const (replicate {n = o} false)
grnd-circuit-correctness {zero} = refl
grnd-circuit-correctness {suc o} = let open ≡-Reasoning in ≡-Reasoning.begin
    ⟦ Gate FALSE ∥ grnd-circuit ⟧[ gσ ]
  ≡⟨ refl ⟩
    parσ (gσ FALSE) ⟦ grnd-circuit ⟧[ gσ ]
  ≡⟨ cong (λ w → parσ (gσ FALSE) w) grnd-circuit-correctness ⟩
    parσ (gσ FALSE) (const (replicate {n = o} false))
  ≡⟨ refl ⟩
    const (replicate {n = suc o} false)
  ∎

translate-correctness : ∀ {i o} → (c : IL[ ΛBoolTrio ] [] i o) → ⟦ translate c ⟧[ gσ ] ≡ eval[ gσ ] c ε
translate-correctness G⟨ g# ⟩ = refl
translate-correctness Grnd = grnd-circuit-correctness
translate-correctness (Plug x) = refl
translate-correctness (x ⟫ y) = let open ≡-Reasoning in ≡-Reasoning.begin
    ⟦ translate x ⟫ translate y ⟧[ gσ ]
  ≡⟨ refl ⟩
    seqσ (⟦ translate x ⟧[ gσ ]) (⟦ translate y ⟧[ gσ ])
  ≡⟨ cong (λ w → seqσ w (⟦ translate y ⟧[ gσ ])) (translate-correctness x) ⟩
    seqσ (eval[ gσ ] x ε) (⟦ translate y ⟧[ gσ ])
  ≡⟨ cong (λ w → seqσ (eval[ gσ ] x ε) w) (translate-correctness y) ⟩
    seqσ (eval[ gσ ] x ε) (eval[ gσ ] y ε)
  ∎
translate-correctness (x ∥ y) = let open ≡-Reasoning in ≡-Reasoning.begin
    ⟦ translate x ∥ translate y ⟧[ gσ ]
  ≡⟨ refl ⟩
    parσ (⟦ translate x ⟧[ gσ ]) (⟦ translate y ⟧[ gσ ])
  ≡⟨ cong (λ w → parσ w (⟦ translate y ⟧[ gσ ])) (translate-correctness x) ⟩
    parσ (eval[ gσ ] x ε) (⟦ translate y ⟧[ gσ ])
  ≡⟨ cong (λ w → parσ (eval[ gσ ] x ε) w) (translate-correctness y) ⟩
    parσ (eval[ gσ ] x ε) (eval[ gσ ] y ε)
  ∎
translate-correctness (Var ())
