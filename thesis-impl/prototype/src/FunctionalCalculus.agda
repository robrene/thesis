module FunctionalCalculus where

open import Data.Unit
open import Data.List
open import Level
open import Function
open import Relation.Binary.PropositionalEquality

data U : Set where
  unit : U
  _⇒_  : U → U → U

infixr 30 _⇒_

⟦_⟧ : U → Set
⟦ unit  ⟧ = ⊤
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

Ctx = List U

-- Simply typed λ-calculus:

data Ref : Ctx → U → Set where
  top : ∀ {Γ τ}   → Ref (τ ∷ Γ) τ
  pop : ∀ {Γ σ τ} → Ref Γ τ → Ref (σ ∷ Γ) τ

data Term : Ctx → U → Set where
  app : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : ∀ {Γ σ τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)
  var : ∀ {Γ τ}   → Ref Γ τ → Term Γ τ

data Env : Ctx → Set where
  nil  : Env []
  cons : ∀ {Γ τ} → ⟦ τ ⟧ → Env Γ → Env (τ ∷ Γ)

_!_ : ∀ {Γ τ} → Env Γ → Ref Γ τ → ⟦ τ ⟧
cons x env ! top     = x
cons x env ! pop ref = env ! ref

eval : ∀ {Γ τ} → Term Γ τ → Env Γ → ⟦ τ ⟧
eval (app t₁ t₂) env = eval t₁ env (eval t₂ env)
eval (lam t)     env = λ x → eval t (cons x env)
eval (var ref)   env = env ! ref

-- SKI combinators:

data SKI : U → Set where
  S   : ∀ {a b c} → SKI ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
  K   : ∀ {a b}   → SKI (a ⇒ b ⇒ a)
  I   : ∀ {a}     → SKI (a ⇒ a)
  _·_ : ∀ {α β}   → SKI (α ⇒ β) → SKI α → SKI β

infixl 30 _·_

apply : ∀ {τ} → SKI τ → ⟦ τ ⟧
apply S x y z   = x z (y z)
apply K x y     = x
apply I x       = x
apply (c₁ · c₂) = apply c₁ (apply c₂)

-- Compiler:

data SKI' : Ctx → U → Set where
  S   : ∀ {Γ a b c} → SKI' Γ ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
  K   : ∀ {Γ a b}   → SKI' Γ (a ⇒ b ⇒ a)
  I   : ∀ {Γ a}     → SKI' Γ (a ⇒ a)
  _·_ : ∀ {Γ α β}   → SKI' Γ (α ⇒ β) → SKI' Γ α → SKI' Γ β
  ⟨_⟩ : ∀ {Γ τ}     → Ref Γ τ → SKI' Γ τ

apply' : ∀ {Γ τ} → SKI' Γ τ → Env Γ → ⟦ τ ⟧
apply' S         env = λ x y z → x z (y z)
apply' K         env = λ x y → x
apply' I         env = λ x → x
apply' (c₁ · c₂) env = apply' c₁ env (apply' c₂ env)
apply' ⟨ ref ⟩   env = env ! ref

closed : ∀ {τ} → SKI' [] τ → SKI τ
closed S = S
closed K = K
closed I = I
closed (c₁ · c₂) = closed c₁ · closed c₂
closed ⟨ () ⟩

lambda : ∀ {Γ σ τ} → SKI' (σ ∷ Γ) τ → SKI' Γ (σ ⇒ τ)
lambda S         = K · S
lambda K         = K · K
lambda I         = K · I
lambda (c₁ · c₂) = S · lambda c₁ · lambda c₂
lambda ⟨ top ⟩   = I
lambda ⟨ pop x ⟩ = K · ⟨ x ⟩

cmp' : ∀ {Γ τ} → Term Γ τ → SKI' Γ τ
cmp' (app t₁ t₂) = cmp' t₁ · cmp' t₂
cmp' (lam t)     = lambda (cmp' t)
cmp' (var x)     = ⟨ x ⟩

cmp : ∀ {τ} → Term [] τ → SKI τ
cmp = closed ∘ cmp'

-- Compiler correctness:

postulate
  fun-ext : Extensionality zero zero

lemma-apply'-lambda : ∀ {Γ σ τ} {env : Env Γ} → (c : SKI' (σ ∷ Γ) τ) → apply' (lambda c) env ≡ (λ x → apply' c (cons x env))
lemma-apply'-lambda S = refl
lemma-apply'-lambda K = refl
lemma-apply'-lambda I = refl
lemma-apply'-lambda {env = env} (c₁ · c₂) = let open ≡-Reasoning in begin
  (λ z → apply' (lambda c₁) env z (apply' (lambda c₂) env z))
    ≡⟨ fun-ext (λ x → cong (apply' (lambda c₁) env x) (cong-app (lemma-apply'-lambda c₂) x)) ⟩
  (λ z → apply' (lambda c₁) env z (apply' c₂ (cons z env)))
    ≡⟨ fun-ext (λ x → cong-app (cong-app (lemma-apply'-lambda c₁) x) (apply' c₂ (cons x env))) ⟩
  (λ z → apply' c₁ (cons z env) (apply' c₂ (cons z env)))
    ∎
lemma-apply'-lambda ⟨ top ⟩ = refl
lemma-apply'-lambda ⟨ pop x ⟩ = refl

lemma-apply'-cons-env : ∀ {Γ σ τ} {env : Env Γ} → (t : Term (σ ∷ Γ) τ) → (x : ⟦ σ ⟧) → apply' (cmp' t) (cons x env) ≡ eval t (cons x env)
lemma-apply'-cons-env {env = env} (app t₁ t₂) x = let open ≡-Reasoning in begin
  apply' (cmp' t₁) (cons x env) (apply' (cmp' t₂) (cons x env))
    ≡⟨ cong-app (lemma-apply'-cons-env t₁ x) (apply' (cmp' t₂) (cons x env)) ⟩
  eval t₁ (cons x env) (apply' (cmp' t₂) (cons x env))
    ≡⟨ cong (eval t₁ (cons x env)) (lemma-apply'-cons-env t₂ x) ⟩
  eval t₁ (cons x env) (eval t₂ (cons x env))
    ∎
lemma-apply'-cons-env {env = env} (lam t) x = let open ≡-Reasoning in begin
  apply' (lambda (cmp' t)) (cons x env)
    ≡⟨ lemma-apply'-lambda (cmp' t) ⟩
  (λ z → apply' (cmp' t) (cons z (cons x env)))
    ≡⟨ fun-ext (λ x₁ → lemma-apply'-cons-env t x₁) ⟩
  (λ z → eval t (cons z (cons x env)))
    ∎
lemma-apply'-cons-env (var top)     _ = refl
lemma-apply'-cons-env (var (pop _)) _ = refl

correct' : ∀ {Γ τ} {env : Env Γ} → (t : Term Γ τ) → apply' (cmp' t) env ≡ eval t env
correct' {env = env} (app t₁ t₂) = let open ≡-Reasoning in begin
  apply' (cmp' t₁) env (apply' (cmp' t₂) env)
    ≡⟨ cong-app (correct' t₁) (apply' (cmp' t₂) env) ⟩
  eval t₁ env (apply' (cmp' t₂) env)
    ≡⟨ cong (eval t₁ env) (correct' t₂) ⟩
  eval t₁ env (eval t₂ env)
    ∎
correct' {env = env} (lam t) = let open ≡-Reasoning in begin
  apply' (lambda (cmp' t)) env
    ≡⟨ lemma-apply'-lambda (cmp' t) ⟩
  (λ x → apply' (cmp' t) (cons x env))
    ≡⟨ fun-ext (lemma-apply'-cons-env t) ⟩
  (λ x → eval t (cons x env))
    ∎
correct' (var x) = refl

lemma-apply'-nil-env : ∀ {τ} → (c : SKI' [] τ) → apply' c nil ≡ apply (closed c)
lemma-apply'-nil-env S = refl
lemma-apply'-nil-env K = refl
lemma-apply'-nil-env I = refl
lemma-apply'-nil-env (c₁ · c₂) = let open ≡-Reasoning in begin
  apply' c₁ nil (apply' c₂ nil)
    ≡⟨ cong (apply' c₁ nil) (lemma-apply'-nil-env c₂) ⟩
  apply' c₁ nil (apply (closed c₂))
    ≡⟨ cong-app (lemma-apply'-nil-env c₁) (apply (closed c₂)) ⟩
  apply (closed c₁) (apply (closed c₂))
    ∎
lemma-apply'-nil-env ⟨ () ⟩

correct : ∀ {τ} → (t : Term [] τ) → apply (cmp t) ≡ eval t nil
correct t = let open ≡-Reasoning in begin
  apply (closed (cmp' t))
    ≡⟨ sym (lemma-apply'-nil-env (cmp' t)) ⟩
  apply' (cmp' t) nil
    ≡⟨ correct' t ⟩
  eval t nil
    ∎
