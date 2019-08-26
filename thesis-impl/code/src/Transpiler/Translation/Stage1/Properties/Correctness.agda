{-# OPTIONS --allow-unsolved-metas #-}

module Transpiler.Translation.Stage1.Properties.Correctness where

open import Function using (_$_; _∘_)
open import Level using (zero)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Extras using (compare₂; lesseq; greater)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using ([]; _∷_; _++_)
open import Data.Vec.Extras using (take; drop)
open import Data.Vec.Properties.Extras using (take-++-identity; drop-++-identity)
open import Data.PolyTypes.Bool
open import Relation.Binary.PropositionalEquality

open import LambdaOne.Environment using (Ctxt; Env; _∷_; _!_)
open import LambdaOne.LambdaOne
open import LambdaOne.Unembedding using (unembed)

open import Transpiler.IntermediateLang.Gates.BoolTrio
open import Transpiler.IntermediateLang.IntermediateLang
open import Transpiler.IntermediateLang.Plugs
open import Transpiler.IntermediateLang.Semantics
open import Transpiler.IntermediateLang.Semantics.BoolTrio using () renaming (ΛBoolTrioσ to gσ)
open import Transpiler.IntermediateLang.Properties.PlugSemantics

open import Transpiler.Util.AtomTranslation using (pad₁; ⤋; ⤊; atomize)
open import Transpiler.Util.AtomTranslation.Properties using (⤊∘⤋-identity)
open import Transpiler.Util.PolyTypeTranslation using (sz; sz-list)

open import Transpiler.Translation.Stage1.EitherBranchingCircuit renaming (circuit to branching-circuit)
open import Transpiler.Translation.Stage1.LambdaOne2IL using (translate)
open import Transpiler.Translation.Stage1.Padding using (left-pad; right-pad)
open import Transpiler.Translation.Stage1.Reduce using (reduce-ctxt; reduce-ctxt-twice)

open import Transpiler.Translation.Stage1.Properties.ReduceCorrectness using (reduce-ctxt-correctness; reduce-ctxt-twice-correctness)

IL : Ctxt → ℕ → ℕ → Set
IL = IL[ ΛBoolTrio ]

postulate
  fun-ext : Extensionality zero zero

mutual
  translate-correctness-ext : ∀ {Γ Δ τ} {env : Env Γ} → (e : Λ₁ Γ Δ τ) → (w : W (sz-list Δ)) → eval[ gσ ] (translate e) env w ≡ atomize {Δ} (unembed e env) w
  translate-correctness-ext ⟨ TRUE  ⟩ []                    = refl
  translate-correctness-ext ⟨ FALSE ⟩ []                    = refl
  translate-correctness-ext ⟨ NOT   ⟩ (false ∷ [])          = refl
  translate-correctness-ext ⟨ NOT   ⟩ (true  ∷ [])          = refl
  translate-correctness-ext ⟨ AND   ⟩ (false ∷ false ∷ [])  = refl
  translate-correctness-ext ⟨ AND   ⟩ (false ∷ true  ∷ [])  = refl
  translate-correctness-ext ⟨ AND   ⟩ (true  ∷ false ∷ [])  = refl
  translate-correctness-ext ⟨ AND   ⟩ (true  ∷ true  ∷ [])  = refl
  translate-correctness-ext ⟨ OR    ⟩ (false ∷ false ∷ [])  = refl
  translate-correctness-ext ⟨ OR    ⟩ (false ∷ true  ∷ [])  = refl
  translate-correctness-ext ⟨ OR    ⟩ (true  ∷ false ∷ [])  = refl
  translate-correctness-ext ⟨ OR    ⟩ (true  ∷ true  ∷ [])  = refl
  translate-correctness-ext #[ r ] [] = refl
  translate-correctness-ext {Δ = Δ} {env = env} (_$₁_ {α = α} f x) w = let open ≡-Reasoning in ≡-Reasoning.begin
      ((eval[ gσ ] (translate f) env) ∘ (parσ (eval[ gσ ] (translate x) env) (plugσ (⇇-id (sz-list Δ))))) w
    ≡⟨ cong₂ (λ z₁ z₂ → (z₁ ∘ (parσ z₂ (plugσ (⇇-id (sz-list Δ))))) w) (translate-correctness f) (translate-correctness x) ⟩
      (atomize {α ∷ Δ} (unembed f env) ∘ (parσ (atomize {[]} (unembed x env)) (plugσ (⇇-id (sz-list Δ))))) w
    ≡⟨ refl ⟩
      (atomize {α ∷ Δ} (unembed f env)) ((atomize {[]} (unembed x env)) (take 0 w) ++ plugσ (⇇-id (sz-list Δ)) (drop 0 w))
    ≡⟨ cong (λ z → (atomize {α ∷ Δ} (unembed f env) (((atomize {[]} (unembed x env)) (take 0 w) ++ z)))) plug-id-semantics-lemma ⟩
      (atomize {α ∷ Δ} (unembed f env)) (atomize {[]} (unembed x env) [] ++ w)
    ≡⟨ refl ⟩
      atomize {Δ} ((unembed f env) $ ⤊ (take (sz α) (⤋ (unembed x env) ++ w))) (drop (sz α) (⤋ (unembed x env) ++ w))
    ≡⟨ cong (λ z → atomize {Δ} ((unembed f env) $ ⤊ (take (sz α) (⤋ (unembed x env) ++ w))) z) (drop-++-identity (⤋ (unembed x env))) ⟩
      atomize {Δ} ((unembed f env) $ ⤊ (take (sz α) (⤋ (unembed x env) ++ w))) w
    ≡⟨ cong (λ z → atomize {Δ} ((unembed f env) $ ⤊ z) w) take-++-identity ⟩
      atomize {Δ} ((unembed f env) $ ⤊ (⤋ (unembed x env))) w
    ≡⟨ cong (λ z → atomize {Δ} ((unembed f env) $ z) w) (⤊∘⤋-identity (unembed x env)) ⟩
      atomize {Δ} ((unembed f env) (unembed x env)) w
    ∎
  translate-correctness-ext {Δ = Δ} {env = env} (letₓ x inₑ e) w = let open ≡-Reasoning in ≡-Reasoning.begin
      ((eval[ gσ ] (reduce-ctxt (translate e)) env) ∘ (parσ (eval[ gσ ] (translate x) env) (plugσ (⇇-id (sz-list Δ))))) w
    ≡⟨ refl ⟩
      (eval[ gσ ] (reduce-ctxt (translate e)) env) ((eval[ gσ ] (translate x) env (take 0 w)) ++ plugσ (⇇-id (sz-list Δ)) (drop 0 w))
    ≡⟨ cong (λ z → (eval[ gσ ] (reduce-ctxt (translate e)) env) (eval[ gσ ] (translate x) env (take 0 w) ++ z)) plug-id-semantics-lemma ⟩
      (eval[ gσ ] (reduce-ctxt (translate e)) env) (eval[ gσ ] (translate x) env [] ++ w)
    ≡⟨ cong ((λ z → (eval[ gσ ] (reduce-ctxt (translate e)) env) (z ++ w))) (translate-correctness-ext x []) ⟩
      (eval[ gσ ] (reduce-ctxt (translate e)) env) (⤋ (unembed x env) ++ w)
    ≡⟨ reduce-ctxt-correctness (translate e) (unembed x env) ⟩
      eval[ gσ ] (translate e) (unembed x env ∷ env) w
    ≡⟨ translate-correctness-ext e w ⟩
      atomize {Δ} (unembed e ((unembed x env) ∷ env)) w
    ∎
  translate-correctness-ext {env = env} (x ,₁ y) [] = let open ≡-Reasoning in ≡-Reasoning.begin
      (eval[ gσ ] (translate x) env []) ++ eval[ gσ ] (translate y) env []
    ≡⟨ cong₂ _++_ (translate-correctness-ext x []) (translate-correctness-ext y []) ⟩
      ⤋ (unembed x env) ++ ⤋ (unembed y env)
    ∎
  translate-correctness-ext {Δ = Δ} {env = env} (case⊗ xy of f) w = let open ≡-Reasoning in ≡-Reasoning.begin
      ((eval[ gσ ] (reduce-ctxt-twice (translate f)) env) ∘ (parσ (eval[ gσ ] (translate xy) env) (plugσ (⇇-id (sz-list Δ))))) w
    ≡⟨ refl ⟩
      (eval[ gσ ] (reduce-ctxt-twice (translate f)) env) ((eval[ gσ ] (translate xy) env (take 0 w)) ++ plugσ (⇇-id (sz-list Δ)) (drop 0 w))
    ≡⟨ cong (λ z → (eval[ gσ ] (reduce-ctxt-twice (translate f)) env) (eval[ gσ ] (translate xy) env (take 0 w) ++ z)) plug-id-semantics-lemma ⟩
      (eval[ gσ ] (reduce-ctxt-twice (translate f)) env) (eval[ gσ ] (translate xy) env [] ++ w)
    ≡⟨ cong ((λ z → (eval[ gσ ] (reduce-ctxt-twice (translate f)) env) (z ++ w))) (translate-correctness-ext xy []) ⟩
      (eval[ gσ ] (reduce-ctxt-twice (translate f)) env) (⤋ (unembed xy env) ++ w)
    ≡⟨ reduce-ctxt-twice-correctness (translate f) (unembed xy env) ⟩
      eval[ gσ ] (translate f) ((proj₁ (unembed xy env)) ∷ (proj₂ (unembed xy env)) ∷ env) w
    ≡⟨ translate-correctness-ext f w ⟩
      atomize {Δ} (unembed f ((proj₁ (unembed xy env)) ∷ (proj₂ (unembed xy env)) ∷ env)) w
    ∎
  translate-correctness-ext {Γ = Γ} {Δ = []} {env = env} (inl₁ {α = α} {β = β} x) [] =
    let open ≡-Reasoning in ≡-Reasoning.begin
      parσ (gσ FALSE) (eval[ gσ ] (left-pad (sz α) (sz β) (translate x)) env) []
    ≡⟨ refl ⟩
      false ∷ (eval[ gσ ] (left-pad (sz α) (sz β) (translate x)) env) []
    ≡⟨ cong (λ z → false ∷ z) (left-pad-lemma α β x) ⟩
      false ∷ pad₁ (sz β) (⤋ (unembed x env))
    ∎
      where
        left-pad-lemma : (α β : Uₚ) → (x : Λ₁ Γ [] α) → eval[ gσ ] (left-pad (sz α) (sz β) (translate x)) env [] ≡ pad₁ (sz β) (⤋ (unembed x env))
        left-pad-lemma α β x with compare₂ (sz α) (sz β)
        ... | cc = {!   !}
  translate-correctness-ext (inr₁ y) w = {!   !}
  translate-correctness-ext (case⊕ xy either f or g) w = {!   !}

  translate-correctness : ∀ {Γ Δ τ} {env : Env Γ} → (e : Λ₁ Γ Δ τ) → eval[ gσ ] (translate e) env ≡ atomize {Δ} (unembed e env)
  translate-correctness e = fun-ext λ w → translate-correctness-ext e w
