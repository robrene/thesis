module Transpiler.Translation.Stage1.EitherBranchingCircuit where

--                      Dup 1            Id 1         Id 1         Id 1
--        xy              ∥               ∥            ∥            ∥
--        ∥      ⟫    Id (a ⊔ b)   ⟫    demux    ⟫    Id a   ⟫    rdc-f      ⟫       mux
--       Id i             ∥               ∥            ∥            ∥
--                       Id i            Id i      Plug♍ b i      rdc-g
--
--                        ,-- 1 ----------------- 1 ------- 1 ------------- 1 --,
--                        |                                                     `--|`````|
--     |``````|-- 1 ------+-- 1 ------|```````|-- a ------- a --|```````|          |     |
--     |  xy  |                       | demux |                 | rdc-f |-- o -----| mux |-- o
--     |______|-- a ⊔ b ----- a ⊔ b --|_______|-- b --, ,-- i --|_______|          |     |
--                                                     ×                        ,--|_____|
-- i ------------ i --------- i ----------------- i --⟨ `-- b --|```````|       |
--                                                     \        | rdc-g |-- o --´
--                                                      `-- i --|_______|

open import Data.Fin using (inject+)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Extras using (_⊔₂_; compare₂; lesseq; greater)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.Vec using () renaming (_++_ to _++ⱽ_; map to mapⱽ)
open import Data.Vec.Extras using (_⇇_)
open import Relation.Binary.PropositionalEquality using (cong)

open import Transpiler.IntermediateLang.Gates.BoolTrio
open import Transpiler.IntermediateLang.IntermediateLang
open import Transpiler.IntermediateLang.Plugs

open import Transpiler.Translation.Stage1.MultiplexerCircuits using (demux; mux)

private
  circuit-s₁ : ∀ {G Γ a b} i → IL[ G ] Γ 0 (1 + (a ⊔₂ b)) → IL[ G ] Γ i (1 + (a ⊔₂ b) + i)
  circuit-s₁ i xy = xy ∥ PlugId i

  circuit-s₂ : ∀ {G Γ} a b i → IL[ G ] Γ (1 + (a ⊔₂ b) + i) (1 + 1 + (a ⊔₂ b) + i)
  circuit-s₂ a b i = PlugDup 1 ∥ PlugId (a ⊔₂ b) ∥ PlugId i

  circuit-s₃ : ∀ {Γ} a b i → IL[ ΛBoolTrio ] Γ (1 + 1 + (a ⊔₂ b) + i) (1 + (a + b) + i)
  circuit-s₃ a b i = PlugId 1 ∥ demux a b ∥ PlugId i

  ⇇-♍ : ∀ b i → (b + i) ⇇ (i + (b + i))
  ⇇-♍ b i rewrite +-comm b i = mapⱽ (inject+ b) (⇇-id i) ++ⱽ ⇇-id (i + b)

  circuit-s₄ : ∀ {G Γ} a b i → IL[ G ] Γ (1 + (a + b) + i) (1 + (a + i) + (b + i))
  circuit-s₄ a b i
      rewrite cong (λ x → 1 + x) (+-assoc a b i)
            | cong (λ x → 1 + x) (+-assoc a i (b + i))
      = PlugId 1 ∥ PlugId a ∥ Plug (⇇-♍ b i)

  circuit-s₅ : ∀ {G Γ a b i o} → IL[ G ] Γ (a + i) o → IL[ G ] Γ (b + i) o → IL[ G ] Γ (1 + (a + i) + (b + i)) (1 + o + o)
  circuit-s₅ rdc-f rdc-g = PlugId 1 ∥ rdc-f ∥ rdc-g

circuit : ∀ {Γ a b i o} → IL[ ΛBoolTrio ] Γ 0 (1 + (a ⊔₂ b)) → IL[ ΛBoolTrio ] Γ (a + i) o → IL[ ΛBoolTrio ] Γ (b + i) o → IL[ ΛBoolTrio ] Γ i o
circuit {_} {a} {b} {i} {o} xy rdc-f rdc-g
    = circuit-s₁ {a = a} i xy ⟫
      circuit-s₂ a b i ⟫
      circuit-s₃ a b i ⟫
      circuit-s₄ a b i ⟫
      circuit-s₅ {a = a} {b = b} rdc-f rdc-g ⟫
      mux o
