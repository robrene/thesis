module Transpiler.Translation.Stage1.MultiplexerCircuits where

open import Function using (_$_)
open import Data.Fin using (inject+)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Extras using (_⊔₂_; compare₂; lesseq; greater; _·2)
open import Data.Nat.Properties using (+-assoc)
open import Data.Vec using () renaming ([] to []ⱽ; _++_ to _++ⱽ_; map to mapⱽ)
open import Data.Vec.Extras using (_⇇_; intersperse-vecs)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import Transpiler.IntermediateLang.Gates.BoolTrio
open import Transpiler.IntermediateLang.IntermediateLang
open import Transpiler.IntermediateLang.Plugs

private
  -- Create duplicated selector wire, where the first one is negated
  mux-s₁ : ∀ {Γ} a → IL[ ΛBoolTrio ] Γ (1 + a + a) ((1 + 1) + a + a)
  mux-s₁ a = (PlugDup 1 ⟫ G⟨ NOT ⟩ ∥ PlugId 1) ∥ PlugId a ∥ PlugId a

  -- Move the selector wires to their respective input groups
  mux-s₂ : ∀ {G Γ} a → IL[ G ] Γ ((1 + 1) + a + a) ((1 + a) + (1 + a))
  mux-s₂ a
      rewrite sym $ +-assoc (1 + a) 1 a
      = PlugId 1 ∥ PlugFlip 1 a ∥ PlugId a

  -- Combines the first wire to all the other wires using logical conjunction
  map-0-and : ∀ {Γ} a → IL[ ΛBoolTrio ] Γ (1 + a) a
  map-0-and zero     = PlugNil 1
  map-0-and (suc n)  = (PlugCopyK 1 1 ⟫ G⟨ AND ⟩ ∥ PlugId 1) ∥ PlugId n ⟫ PlugId 1 ∥ map-0-and n

  -- Zero out the unselected input group
  mux-s₃ : ∀ {Γ} a → IL[ ΛBoolTrio ] Γ ((1 + a) + (1 + a)) (a + a)
  mux-s₃ a = map-0-and a ∥ map-0-and a

  -- Reordering of wires to intersperse the input groups
  ⇇-χ : ∀ n → (n + n) ⇇ (n ·2)
  ⇇-χ n = intersperse-vecs (mapⱽ (inject+ n) (⇇-id n)) (mapⱽ (inject+ n) (⇇-id n))

  -- Combines an even number of wires using logical disjunction
  map-pairwise-or : ∀ {Γ} a → IL[ ΛBoolTrio ] Γ (a ·2) a
  map-pairwise-or zero     = Grnd
  map-pairwise-or (suc a)  = G⟨ OR ⟩ ∥ map-pairwise-or a

  -- Output only the selected input group
  mux-s₄ : ∀ {Γ} a → IL[ ΛBoolTrio ] Γ (a + a) a
  mux-s₄ a = Plug (⇇-χ a) ⟫ map-pairwise-or a

-- Multiplexer - Select an input group based on the first wire
-- If the first wire sends the FALSE signal, the first group is output
-- If the first wire sends the TRUE signal, the second group is output
mux : ∀ {Γ} a → IL[ ΛBoolTrio ] Γ (1 + a + a) a
mux a = mux-s₁ a ⟫ mux-s₂ a ⟫ mux-s₃ a ⟫ mux-s₄ a

private
  -- Input wires are of a size indexed by a _⊔₂_ term
  ⇇-smartdup : ∀ a b → (a ⊔₂ b) ⇇ (a + b)
  ⇇-smartdup a b with compare₂ a b
  ⇇-smartdup a            .(a + k) | lesseq .a k  = mapⱽ (inject+ k) (⇇-id a) ++ⱽ (⇇-id (a + k))
  ⇇-smartdup .(b + suc k) b        | greater .b k = (⇇-id (b + suc k)) ++ⱽ mapⱽ (inject+ (suc k)) (⇇-id b)

  -- Create duplicated selector wire, where the first one is negated
  -- Also duplicate the input wires into two output groups
  demux-s₁ : ∀ {Γ} a b → IL[ ΛBoolTrio ] Γ (1 + (a ⊔₂ b)) ((1 + 1) + a + b)
  demux-s₁ a b = (PlugDup 1 ⟫ G⟨ NOT ⟩ ∥ PlugId 1) ∥ Plug (⇇-smartdup a b)

  -- Move the selector wires to their respective output groups
  demux-s₂ : ∀ {G Γ} a b → IL[ G ] Γ ((1 + 1) + a + b) ((1 + a) + (1 + b))
  demux-s₂ a b
      rewrite sym $ +-assoc (1 + a) 1 b
      = PlugId 1 ∥ PlugFlip 1 a ∥ PlugId b

  -- Zero out the unselected output group
  demux-s₃ : ∀ {Γ} a b → IL[ ΛBoolTrio ] Γ ((1 + a) + (1 + b)) (a + b)
  demux-s₃ a b = map-0-and a ∥ map-0-and b

-- Smart demultiplexer - Output the input signal to one of two output groups
-- If the first wire sends the FALSE signal, the input group must be of size `a`
-- The input signal is then output to the first `a` wires of the output, with the other outputs FALSE
-- If the first wire sends the TRUE signal, the input group must be of size `b`
-- The input signal is then output to the last `b` wires of the output, with the other outputs FALSE
demux : ∀ {Γ} a b → IL[ ΛBoolTrio ] Γ (1 + (a ⊔₂ b)) (a + b)
demux a b = demux-s₁ a b ⟫ demux-s₂ a b ⟫ demux-s₃ a b
