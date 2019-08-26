module Transpiler.IntermediateLang.Properties.PlugSemantics where

open import Function
open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Vec
open import Data.Vec.Properties using (lookup∘tabulate; tabulate∘lookup)
open import Data.Vec.Properties.Extras using (tabulate-ext; lookup-allFin-id-lemma; lookup-allFin-dup-lemma; lookup-allFin-copyk-lemma)
open import Relation.Binary.PropositionalEquality

open import Transpiler.IntermediateLang.Plugs
open import Transpiler.IntermediateLang.Semantics

plug-id-semantics-lemma : ∀ {k} {w : W k} → plugσ (⇇-id k) w ≡ w
plug-id-semantics-lemma {k} {w} = let open ≡-Reasoning in ≡-Reasoning.begin
   tabulate (λ x → lookup (lookup x (allFin k)) w)
  ≡⟨ tabulate-ext (λ x → lookup (lookup x (allFin k)) w) (λ x → lookup x w) (λ i → lookup-allFin-id-lemma i w ) ⟩
    tabulate (λ x → lookup x w)
  ≡⟨ tabulate∘lookup w ⟩
    w
  ∎

plug-dup-semantics-lemma : ∀ {k} {w : W k} → plugσ (⇇-dup k) w ≡ w ++ w
plug-dup-semantics-lemma {k} {w} = let open ≡-Reasoning in ≡-Reasoning.begin
    tabulate (λ x → lookup (lookup x (allFin k ++ allFin k)) w)
  ≡⟨ tabulate-ext (λ x → lookup (lookup x (allFin k ++ allFin k)) w) (λ x → lookup x (w ++ w)) (λ i → lookup-allFin-dup-lemma i w) ⟩
    tabulate (λ x → lookup x (w ++ w))
  ≡⟨ tabulate∘lookup (w ++ w) ⟩
    w ++ w
  ∎

plug-copyk-semantics-lemma : ∀ {n k} {w : W n} {w₀ : W k} → plugσ (⇇-copyk n k) (w₀ ++ w) ≡ ((w₀ ++ w) ++ w₀)
plug-copyk-semantics-lemma {n} {k} {w} {w₀} = let open ≡-Reasoning in ≡-Reasoning.begin
    tabulate (λ x → lookup (lookup x (allFin (k + n) ++ tabulate (inject+ n))) (w₀ ++ w))
  ≡⟨ tabulate-ext (λ x → lookup (lookup x (allFin (k + n) ++ tabulate (inject+ n))) (w₀ ++ w)) (λ x → lookup x ((w₀ ++ w) ++ w₀)) (λ i → lookup-allFin-copyk-lemma i w₀ w) ⟩
    tabulate (λ x → lookup x ((w₀ ++ w) ++ w₀))
  ≡⟨ tabulate∘lookup ((w₀ ++ w) ++ w₀) ⟩
    (w₀ ++ w) ++ w₀
  ∎
