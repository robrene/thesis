module Data.Vec.Properties.Extras where

open import Function using (_$_; id)
open import Data.Fin hiding (_+_)
open import Data.Fin.Extras
open import Data.Nat
open import Data.Product
open import Data.Vec hiding (take; drop)
open import Data.Vec.Extras using (coerce-vec; take; drop)
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality

tabulate-ext : ∀ {a} {A : Set a} {k} → (f g : Fin k → A) → ((i : Fin k) → f i ≡ g i) → tabulate f ≡ tabulate g
tabulate-ext {k = zero}  f g H = refl
tabulate-ext {k = suc k} f g H rewrite H zero = cong (λ xs → g zero ∷ xs) (tabulate-ext (λ i → f (suc i)) (λ i → g (suc i)) (λ i → H (suc i)))

take-++-identity : ∀ {a} {A : Set a} {m n} {v₁ : Vec A m} {v₂ : Vec A n} → take m (v₁ ++ v₂) ≡ v₁
take-++-identity {m = zero}  {v₁ = []}     = refl
take-++-identity {m = suc m} {v₁ = x ∷ v₁} = cong (λ z → x ∷ z) take-++-identity

drop-++-identity : ∀ {a} {A : Set a} {m n} (v₁ : Vec A m) {v₂ : Vec A n} → drop m (v₁ ++ v₂) ≡ v₂
drop-++-identity {m = zero}  []       = refl
drop-++-identity {m = suc m} (x ∷ v₁) = drop-++-identity v₁

take-drop-identity : ∀ {a} {A : Set a} {m n} {v : Vec A (m + n)} → take m v ++ drop m v ≡ v
take-drop-identity {m = zero} = refl
take-drop-identity {m = suc m} {v = x ∷ v} = cong (λ z → x ∷ z) (take-drop-identity {m = m} {v = v})

lookup-inject+-lemma : ∀ {a} {A : Set a} {k n} →
                       (i : Fin k) → (v : Vec A k) → (vₙ : Vec A n) →
                       lookup (inject+ n i) (v ++ vₙ) ≡ lookup i v
lookup-inject+-lemma {k = zero} () v _
lookup-inject+-lemma {k = suc k} zero (x ∷ v) _ = refl
lookup-inject+-lemma {k = suc k} (suc i) (x ∷ v) _ = lookup-inject+-lemma i v _

lookup-allFin-id-lemma : ∀ {a} {A : Set a} {k} → (i : Fin k) → (v : Vec A k) → lookup (lookup i (allFin k)) v ≡ lookup i v
lookup-allFin-id-lemma {k = k} i v = cong (λ z → lookup z v) (lookup∘tabulate id i)

lookup-finl-lemma : ∀ {a} {A : Set a} {m n : ℕ} →
                    (i : Fin m) → (vₘ : Vec A m) → (vₙ : Vec A n) →
                    lookup (finl m n i) (vₘ ++ vₙ) ≡ lookup i vₘ
lookup-finl-lemma {m = zero} {n} () vₘ vₙ
lookup-finl-lemma {m = suc m} {n} zero (x ∷ vₘ) vₙ = refl
lookup-finl-lemma {m = suc m} {n} (suc i) (x ∷ vₘ) vₙ = lookup-finl-lemma i vₘ vₙ

lookup-finr-lemma : ∀ {a} {A : Set a} {m n : ℕ} →
                    (i : Fin n) → (vₘ : Vec A m) → (vₙ : Vec A n) →
                    lookup (finr m n i) (vₘ ++ vₙ) ≡ lookup i vₙ
lookup-finr-lemma {m = zero} {n} i [] vₙ = refl
lookup-finr-lemma {m = suc m} {n} i (x ∷ vₘ) vₙ = lookup-finr-lemma i vₘ vₙ

lookup-allFin-dup-lemma : ∀ {a} {A : Set a} {k} → (i : Fin (k + k)) → (v : Vec A k) → lookup (lookup i (allFin k ++ allFin k)) v ≡ lookup i (v ++ v)
lookup-allFin-dup-lemma {k = k} i v with finPlus k k i
lookup-allFin-dup-lemma {k = k} .(finl k k i) v | isfinl i = let open ≡-Reasoning in ≡-Reasoning.begin
    lookup (lookup (finl k k i) (allFin k ++ allFin k)) v
  ≡⟨ cong (λ z → lookup z v) (lookup-finl-lemma i (allFin k) (allFin k)) ⟩
    lookup (lookup i (allFin k)) v
  ≡⟨ lookup-allFin-id-lemma i v ⟩
    lookup i v
  ≡⟨ sym $ lookup-finl-lemma i v v ⟩
    lookup (finl k k i) (v ++ v)
  ∎
lookup-allFin-dup-lemma {k = k} .(finr k k i) v | isfinr i = let open ≡-Reasoning in ≡-Reasoning.begin
    lookup (lookup (finr k k i) (allFin k ++ allFin k)) v
  ≡⟨ cong (λ z → lookup z v) (lookup-finr-lemma i (allFin k) (allFin k)) ⟩
    lookup (lookup i (allFin k)) v
  ≡⟨ lookup-allFin-id-lemma i v ⟩
    lookup i v
  ≡⟨ sym $ lookup-finr-lemma i v v ⟩
    lookup (finr k k i) (v ++ v)
  ∎

lookup-allFin-copyk-lemma : ∀ {a} {A : Set a} {k n} →
                            (i : Fin (k + n + k)) → (v₀ : Vec A k) → (v : Vec A n) →
                            lookup (lookup i (allFin (k + n) ++ tabulate (inject+ n))) (v₀ ++ v) ≡ lookup i ((v₀ ++ v) ++ v₀)
lookup-allFin-copyk-lemma {k = k} {n = n} i v₀ v with finPlus (k + n) k i
lookup-allFin-copyk-lemma {k = k} {n = n} .(finl (k + n) k i) v₀ v | isfinl i = let open ≡-Reasoning in ≡-Reasoning.begin
    lookup (lookup (finl (k + n) k i) (allFin (k + n) ++ tabulate (inject+ n))) (v₀ ++ v)
  ≡⟨ cong (λ z → lookup z (v₀ ++ v)) (lookup-finl-lemma i (allFin (k + n)) (tabulate (inject+ n))) ⟩
    lookup (lookup i (allFin (k + n))) (v₀ ++ v)
  ≡⟨ lookup-allFin-id-lemma i (v₀ ++ v) ⟩
    lookup i (v₀ ++ v)
  ≡⟨ sym $ lookup-finl-lemma i (v₀ ++ v) v₀ ⟩
    lookup (finl (k + n) k i) ((v₀ ++ v) ++ v₀)
  ∎
lookup-allFin-copyk-lemma {k = k} {n = n} .(finr (k + n) k i) v₀ v | isfinr i = let open ≡-Reasoning in ≡-Reasoning.begin
    lookup (lookup (finr (k + n) k i) (allFin (k + n) ++ tabulate (inject+ n))) (v₀ ++ v)
  ≡⟨ cong (λ z → lookup z (v₀ ++ v)) (lookup-finr-lemma i (allFin (k + n)) (tabulate (inject+ n))) ⟩
    lookup (lookup i (tabulate (inject+ n))) (v₀ ++ v)
  ≡⟨ cong (λ z → lookup z (v₀ ++ v)) (lookup∘tabulate (inject+ n) i) ⟩
    lookup (inject+ n i) (v₀ ++ v)
  ≡⟨ lookup-inject+-lemma i v₀ v ⟩
    lookup i v₀
  ≡⟨ cong (λ z → lookup z v₀) (sym $ lookup∘tabulate id i) ⟩
    lookup (lookup i (allFin k)) v₀
  ≡⟨ lookup-allFin-id-lemma i v₀ ⟩
    lookup i v₀
  ≡⟨ sym $ lookup-finr-lemma i (v₀ ++ v) v₀ ⟩
    lookup (finr (k + n) k i) ((v₀ ++ v) ++ v₀)
  ∎
