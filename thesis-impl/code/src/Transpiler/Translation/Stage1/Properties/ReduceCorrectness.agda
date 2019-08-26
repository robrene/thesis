{-# OPTIONS --allow-unsolved-metas #-}

module Transpiler.Translation.Stage1.Properties.ReduceCorrectness where

open import Function using (_$_; _∘_; const)
open import Data.List using (_∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-right-identity; +-assoc)
open import Data.PolyTypes.Bool
open import Data.Product using (proj₁; proj₂)
open import Data.Vec using ([]; _∷_; _++_; replicate)
open import Data.Vec.Extras using (coerce-vec; take; drop)
open import Data.Vec.Properties.Extras using (take-++-identity; drop-++-identity)
open import Data.Vec.Properties.Coercion using (take-++-identity-c+a; drop-++-identity-c+a; take-++-identity-c+sa; drop-++-identity-c+sa; uncoerce-vec-++-[] )
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Extras using (sym-sym-relation)

open import LambdaOne.Environment using (Env; _∷_; top; pop)

open import Transpiler.IntermediateLang.Coerce
open import Transpiler.IntermediateLang.IntermediateLang
open import Transpiler.IntermediateLang.Plugs
open import Transpiler.IntermediateLang.Semantics
open import Transpiler.IntermediateLang.Properties.CoercionSemantics
open import Transpiler.IntermediateLang.Properties.PlugSemantics

open import Transpiler.Util.AtomTranslation using (⤋)
open import Transpiler.Util.PolyTypeTranslation using (sz)

open import Transpiler.Translation.Stage1.CombinatorCircuits
open import Transpiler.Translation.Stage1.Reduce

reduce-ctxt-correctness : ∀ {G τ Γ i o} {gσ : Gateσ G} {env : Env Γ} {w : W i} → (e : IL[ G ] (τ ∷ Γ) i o) → (x : Tₚ τ) → (eval[ gσ ] (reduce-ctxt e) env (⤋ x ++ w)) ≡ (eval[ gσ ] e (x ∷ env) w)
reduce-ctxt-correctness {τ = τ} {gσ = gσ} {w = w} G⟨ g# ⟩ x = let open ≡-Reasoning in ≡-Reasoning.begin
    parσ (plugσ (⇇-nil (sz τ))) (gσ g#) (⤋ x ++ w)
  ≡⟨ refl ⟩
    plugσ (⇇-nil (sz τ)) (take (sz τ) (⤋ x ++ w)) ++ (gσ g#) (drop (sz τ) (⤋ x ++ w))
  ≡⟨ refl ⟩
    (gσ g#) (drop (sz τ) (⤋ x ++ w))
  ≡⟨ cong (λ z → (gσ g#) z) (drop-++-identity (⤋ x)) ⟩
    gσ g# w
  ∎
reduce-ctxt-correctness Grnd x = refl
reduce-ctxt-correctness {τ = τ} {w = w} (Plug p) x = let open ≡-Reasoning in ≡-Reasoning.begin
    parσ (plugσ (⇇-nil (sz τ))) (plugσ p) (⤋ x ++ w)
  ≡⟨ refl ⟩
    plugσ (⇇-nil (sz τ)) (take (sz τ) (⤋ x ++ w)) ++ (plugσ p) (drop (sz τ) (⤋ x ++ w))
  ≡⟨ refl ⟩
    (plugσ p) (drop (sz τ) (⤋ x ++ w))
  ≡⟨ cong (λ z → (plugσ p) z) (drop-++-identity (⤋ x)) ⟩
    plugσ p w
  ∎
reduce-ctxt-correctness {τ = τ} {i = i} {gσ = gσ} {env = env} {w = w} (c₁ ⟫ c₂) x = let open ≡-Reasoning in ≡-Reasoning.begin
    seqσ (seqσ (eval[ gσ ] (S-bypass (sz τ) i) env) (parσ (plugσ (⇇-id (sz τ))) (eval[ gσ ] (reduce-ctxt c₁) env))) (eval[ gσ ] (reduce-ctxt c₂) env) (⤋ x ++ w)
  ≡⟨ refl ⟩
    (eval[ gσ ] (reduce-ctxt c₂) env)
    (parσ
      (plugσ (⇇-id (sz τ)))
      (eval[ gσ ] (reduce-ctxt c₁) env)
        (eval[ gσ ] (S-bypass (sz τ) i) env (⤋ x ++ w)))
  ≡⟨ refl ⟩
    (eval[ gσ ] (reduce-ctxt c₂) env)
      ((plugσ (⇇-id (sz τ))) (take (sz τ) (eval[ gσ ] (S-bypass (sz τ) i) env (⤋ x ++ w))) ++
      (eval[ gσ ] (reduce-ctxt c₁) env) (drop (sz τ) (eval[ gσ ] (S-bypass (sz τ) i) env (⤋ x ++ w))))
  ≡⟨ cong (λ z → (eval[ gσ ] (reduce-ctxt c₂) env) (z ++ (eval[ gσ ] (reduce-ctxt c₁) env) (drop (sz τ) (eval[ gσ ] (S-bypass (sz τ) i) env (⤋ x ++ w))))) (plug-id-semantics-lemma {sz τ}) ⟩
    (eval[ gσ ] (reduce-ctxt c₂) env)
      ((take (sz τ) (eval[ gσ ] (S-bypass (sz τ) i) env (⤋ x ++ w))) ++
      ((eval[ gσ ] (reduce-ctxt c₁) env) (drop (sz τ) (eval[ gσ ] (S-bypass (sz τ) i) env (⤋ x ++ w)))))
  ≡⟨ cong₂ (λ z₁ z₂ → (eval[ gσ ] (reduce-ctxt c₂) env) (z₁ ++ eval[ gσ ] (reduce-ctxt c₁) env z₂)) (take-S-bypass-lemma (⤋ x)) (drop-S-bypass-lemma (⤋ x)) ⟩
    eval[ gσ ] (reduce-ctxt c₂) env (⤋ x ++ eval[ gσ ] (reduce-ctxt c₁) env (⤋ x ++ w))
  ≡⟨ reduce-ctxt-correctness c₂ x ⟩
    eval[ gσ ] c₂ (x ∷ env) (eval[ gσ ] (reduce-ctxt c₁) env (⤋ x ++ w))
  ≡⟨ cong (λ z → eval[ gσ ] c₂ (x ∷ env) z) (reduce-ctxt-correctness c₁ x) ⟩
    (eval[ gσ ] c₂ (x ∷ env)) ((eval[ gσ ] c₁ (x ∷ env)) w)
  ≡⟨ refl ⟩
    seqσ (eval[ gσ ] c₁ (x ∷ env)) (eval[ gσ ] c₂ (x ∷ env)) w
  ∎
    where
      take-S-bypass-lemma : ∀ {k} (a : W k) → take k (eval[ gσ ] (S-bypass k i) env (a ++ w)) ≡ a
      take-S-bypass-lemma {k} a = let open ≡-Reasoning in ≡-Reasoning.begin
          take k (eval[ gσ ] (S-bypass k i) env (a ++ w))
        ≡⟨ cong (take k) (coerceₒ-semantics-lemma (+-assoc k k i) (PlugDup k ∥ PlugId i)) ⟩
          take k (coerce-vec (+-assoc k k i) (eval[ gσ ] (PlugDup k ∥ PlugId i) env (a ++ w)))
        ≡⟨ refl ⟩
          take k (coerce-vec (+-assoc k k i) $ eval[ gσ ] (PlugDup k) env (take k (a ++ w)) ++ eval[ gσ ] (PlugId i) env (drop k (a ++ w)))
        ≡⟨ cong₂ (λ z₁ z₂ → take k (coerce-vec (+-assoc k k i) $ z₁ ++ z₂)) plug-dup-semantics-lemma plug-id-semantics-lemma ⟩
          take k (coerce-vec (+-assoc k k i) $ ((take k (a ++ w)) ++ (take k (a ++ w))) ++ (drop k (a ++ w)))
        ≡⟨ cong₂ (λ z₁ z₂ → take k (coerce-vec (+-assoc k k i) $ (z₁ ++ z₁) ++ z₂)) take-++-identity (drop-++-identity a) ⟩
          take k (coerce-vec (+-assoc k k i) $ (a ++ a) ++ w)
        ≡⟨ take-++-identity-c+a {m = k} {k₀ = k} {k₁ = i} a a w ⟩
          a
        ∎
      drop-S-bypass-lemma : ∀ {k} (a : W k) → drop k (eval[ gσ ] (S-bypass k i) env (a ++ w)) ≡ a ++ w
      drop-S-bypass-lemma {k} a = let open ≡-Reasoning in ≡-Reasoning.begin
          drop k (eval[ gσ ] (S-bypass k i) env (a ++ w))
        ≡⟨ cong (drop k) (coerceₒ-semantics-lemma (+-assoc k k i) (PlugDup k ∥ PlugId i)) ⟩
          drop k (coerce-vec (+-assoc k k i) (eval[ gσ ] (PlugDup k ∥ PlugId i) env (a ++ w)))
        ≡⟨ refl ⟩
          drop k (coerce-vec (+-assoc k k i) $ eval[ gσ ] (PlugDup k) env (take k (a ++ w)) ++ eval[ gσ ] (PlugId i) env (drop k (a ++ w)))
        ≡⟨ cong₂ (λ z₁ z₂ → drop k (coerce-vec (+-assoc k k i) $ z₁ ++ z₂)) plug-dup-semantics-lemma plug-id-semantics-lemma ⟩
          drop k (coerce-vec (+-assoc k k i) $ ((take k (a ++ w)) ++ (take k (a ++ w))) ++ (drop k (a ++ w)))
        ≡⟨ cong₂ (λ z₁ z₂ → drop k (coerce-vec (+-assoc k k i) $ (z₁ ++ z₁) ++ z₂)) take-++-identity (drop-++-identity a) ⟩
          drop k (coerce-vec (+-assoc k k i) $ (a ++ a) ++ w)
        ≡⟨ drop-++-identity-c+a {m = k} {k₀ = k} {k₁ = i} a a w ⟩
          a ++ w
        ∎
reduce-ctxt-correctness {τ = τ} {gσ = gσ} {env = env} {w = w} (_∥_ {i₁ = i₁} {i₂ = i₂} a b) x = let open ≡-Reasoning in ≡-Reasoning.begin
    seqσ (eval[ gσ ] (P-insert (sz τ) i₁ i₂) env)
         (parσ (eval[ gσ ] (reduce-ctxt a) env)
               (eval[ gσ ] (reduce-ctxt b) env))
         (⤋ x ++ w)
  ≡⟨ refl ⟩
    (eval[ gσ ] (reduce-ctxt a) env) (take (sz τ + i₁) ((eval[ gσ ] (P-insert (sz τ) i₁ i₂) env) (⤋ x ++ w))) ++
    (eval[ gσ ] (reduce-ctxt b) env) (drop (sz τ + i₁) ((eval[ gσ ] (P-insert (sz τ) i₁ i₂) env) (⤋ x ++ w)))
  ≡⟨ cong₂ (λ z₁ z₂ → (eval[ gσ ] (reduce-ctxt a) env) z₁ ++ (eval[ gσ ] (reduce-ctxt b) env) z₂) (take-P-insert-lemma (⤋ x)) (drop-P-insert-lemma (⤋ x)) ⟩
    (eval[ gσ ] (reduce-ctxt a) env) (⤋ x ++ (take i₁ w)) ++
    (eval[ gσ ] (reduce-ctxt b) env) (⤋ x ++ (drop i₁ w))
  ≡⟨ cong₂ _++_ (reduce-ctxt-correctness a x) (reduce-ctxt-correctness b x) ⟩
    (eval[ gσ ] a (x ∷ env)) (take i₁ w) ++
    (eval[ gσ ] b (x ∷ env)) (drop i₁ w)
  ≡⟨ refl ⟩
    parσ (eval[ gσ ] a (x ∷ env)) (eval[ gσ ] b (x ∷ env)) w
  ∎
    where
      take-P-insert-lemma : ∀ {k} (a : W k) → take (k + i₁) ((eval[ gσ ] (P-insert k i₁ i₂) env) (a ++ w)) ≡ a ++ (take i₁ w)
      take-P-insert-lemma {k} a = let open ≡-Reasoning in ≡-Reasoning.begin
          take (k + i₁) ((eval[ gσ ] (P-insert k i₁ i₂) env) (a ++ w))
        ≡⟨ cong (take (k + i₁)) (coerceᵢₒ-semantics-lemma (+-assoc k i₁ i₂) (+-assoc (k + i₁) k i₂) (PlugCopyK i₁ k ∥ PlugId i₂)) ⟩
          take (k + i₁) (coerce-vec (+-assoc (k + i₁) k i₂) (eval[ gσ ] (PlugCopyK i₁ k ∥ PlugId i₂) env (coerce-vec (sym $ +-assoc k i₁ i₂) (a ++ w))))
        ≡⟨ cong₂ (λ z₁ z₂ → take (k + i₁) (coerce-vec (+-assoc (k + i₁) k i₂) $ z₁ ++ z₂)) plug-copyk-semantics-lemma plug-id-semantics-lemma ⟩
          take (k + i₁) (coerce-vec (+-assoc (k + i₁) k i₂)
            (eval[ gσ ] (PlugCopyK i₁ k) env (take (k + i₁) (coerce-vec (sym $ +-assoc k i₁ i₂) (a ++ w))) ++
            (eval[ gσ ] (PlugId i₂) env (drop (k + i₁) (coerce-vec (sym $ +-assoc k i₁ i₂) (a ++ w))))))
        ≡⟨ cong₂ (λ z₁ z₂ → take (k + i₁) (coerce-vec (+-assoc (k + i₁) k i₂) ((eval[ gσ ] (PlugCopyK i₁ k) env z₁) ++ (eval[ gσ ] (PlugId i₂) env z₂))))
                 (take-++-identity-c+sa a w) (drop-++-identity-c+sa a w) ⟩
          take (k + i₁) (coerce-vec (+-assoc (k + i₁) k i₂)
            (eval[ gσ ] (PlugCopyK i₁ k) env (a ++ take i₁ w) ++
            (eval[ gσ ] (PlugId i₂) env (drop i₁ w))))
        ≡⟨ cong₂ (λ z₁ z₂ → take (k + i₁) (coerce-vec (+-assoc (k + i₁) k i₂) (z₁ ++ z₂))) plug-copyk-semantics-lemma plug-id-semantics-lemma ⟩
          take (k + i₁) (coerce-vec (+-assoc (k + i₁) k i₂)
            (((a ++ take i₁ w) ++ a) ++ drop i₁ w))
        ≡⟨ take-++-identity-c+a (a ++ take i₁ w) a (drop i₁ w) ⟩
          a ++ take i₁ w
        ∎
      drop-P-insert-lemma : ∀ {k} (a : W k) → drop (k + i₁) ((eval[ gσ ] (P-insert k i₁ i₂) env) (a ++ w)) ≡ a ++ (drop i₁ w)
      drop-P-insert-lemma {k} a = let open ≡-Reasoning in ≡-Reasoning.begin
          drop (k + i₁) ((eval[ gσ ] (P-insert k i₁ i₂) env) (a ++ w))
        ≡⟨ cong (drop (k + i₁)) (coerceᵢₒ-semantics-lemma (+-assoc k i₁ i₂) (+-assoc (k + i₁) k i₂) (PlugCopyK i₁ k ∥ PlugId i₂)) ⟩
          drop (k + i₁) (coerce-vec (+-assoc (k + i₁) k i₂) (eval[ gσ ] (PlugCopyK i₁ k ∥ PlugId i₂) env (coerce-vec (sym $ +-assoc k i₁ i₂) (a ++ w))))
        ≡⟨ cong₂ (λ z₁ z₂ → drop (k + i₁) (coerce-vec (+-assoc (k + i₁) k i₂) $ z₁ ++ z₂)) plug-copyk-semantics-lemma plug-id-semantics-lemma ⟩
          drop (k + i₁) (coerce-vec (+-assoc (k + i₁) k i₂)
            (eval[ gσ ] (PlugCopyK i₁ k) env (take (k + i₁) (coerce-vec (sym $ +-assoc k i₁ i₂) (a ++ w))) ++
            (eval[ gσ ] (PlugId i₂) env (drop (k + i₁) (coerce-vec (sym $ +-assoc k i₁ i₂) (a ++ w))))))
        ≡⟨ cong₂ (λ z₁ z₂ → drop (k + i₁) (coerce-vec (+-assoc (k + i₁) k i₂) ((eval[ gσ ] (PlugCopyK i₁ k) env z₁) ++ (eval[ gσ ] (PlugId i₂) env z₂))))
                 (take-++-identity-c+sa a w) (drop-++-identity-c+sa a w) ⟩
          drop (k + i₁) (coerce-vec (+-assoc (k + i₁) k i₂)
            (eval[ gσ ] (PlugCopyK i₁ k) env (a ++ take i₁ w) ++
            (eval[ gσ ] (PlugId i₂) env (drop i₁ w))))
        ≡⟨ cong₂ (λ z₁ z₂ → drop (k + i₁) (coerce-vec (+-assoc (k + i₁) k i₂) (z₁ ++ z₂))) plug-copyk-semantics-lemma plug-id-semantics-lemma ⟩
          drop (k + i₁) (coerce-vec (+-assoc (k + i₁) k i₂)
            (((a ++ take i₁ w) ++ a) ++ drop i₁ w))
        ≡⟨ drop-++-identity-c+a (a ++ take i₁ w) a (drop i₁ w) ⟩
          a ++ drop i₁ w
        ∎
reduce-ctxt-correctness {τ = τ} {gσ = gσ} {env = env} {w = []} (Var top) x = let open ≡-Reasoning in ≡-Reasoning.begin
    eval[ gσ ] (coerceᵢ (sym $ +-right-identity (sz τ)) (Plug (⇇-id (sz τ)))) env (⤋ x ++ [])
  ≡⟨ coerceᵢ-semantics-lemma (sym $ +-right-identity (sz τ)) (Plug (⇇-id (sz τ))) ⟩
    eval[ gσ ] (Plug (⇇-id (sz τ))) env (coerce-vec (sym $ sym $ +-right-identity (sz τ)) (⤋ x ++ []))
  ≡⟨ plug-id-semantics-lemma ⟩
    coerce-vec (sym (sym (+-right-identity (sz τ)))) (⤋ x ++ [])
  ≡⟨ cong (λ z → coerce-vec z (⤋ x ++ [])) (sym-sym-relation (+-right-identity (sz τ))) ⟩
    coerce-vec (+-right-identity (sz τ)) (⤋ x ++ [])
  ≡⟨ uncoerce-vec-++-[] (+-right-identity (sz τ)) (⤋ x) ⟩
    ⤋ x
  ∎
reduce-ctxt-correctness {w = []} (Var (pop i)) x = refl

reduce-ctxt-twice-correctness : ∀ {G α β Γ i o} {gσ : Gateσ G} {env : Env Γ} {w : W i} → (f : IL[ G ] (α ∷ β ∷ Γ) i o) → (xy : Tₚ (α ⊗ β)) → (eval[ gσ ] (reduce-ctxt-twice f) env (⤋ xy ++ w)) ≡ (eval[ gσ ] f (proj₁ xy ∷ proj₂ xy ∷ env) w)
reduce-ctxt-twice-correctness {α = α} {β = β} {i = i} {o = o} {gσ = gσ} {env = env} {w = w} f xy = let open ≡-Reasoning in ≡-Reasoning.begin
    eval[ gσ ] (reduce-ctxt-twice f) env (⤋ xy ++ w)
  ≡⟨ refl ⟩
    seqσ (eval[ gσ ] (coerceₒ (+-assoc (sz β) (sz α) i) (PlugFlip (sz α) (sz β) ∥ PlugId i)) env)
         (eval[ gσ ] (reduce-ctxt (reduce-ctxt f)) env)
         (⤋ xy ++ w)
  ≡⟨ cong (λ z → seqσ z (eval[ gσ ] (reduce-ctxt (reduce-ctxt f)) env) (⤋ xy ++ w)) {! coerceₒ-semantics-lemma ? ?  !} ⟩
    {!   !}
  ≡⟨ {!   !} ⟩
    eval[ gσ ] f (proj₁ xy ∷ proj₂ xy ∷ env) w
  ∎
