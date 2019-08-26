module Data.Environment (Ty : Set) where

open import Data.List using (List; []; _∷_)

Ctxt : Set
Ctxt = List Ty

data Env (F : Ty → Set) : Ctxt → Set where
  ε    : Env F []
  _∷_  : ∀ {Γ a} → F a → Env F Γ → Env F (a ∷ Γ)

infixr 5 _∷_

open Env public

data Ref : Ctxt → Ty → Set where
  top  : ∀ {Γ a}    → Ref (a ∷ Γ) a
  pop  : ∀ {Γ a b}  → Ref Γ b → Ref (a ∷ Γ) b

open Ref public

_!_ : ∀ {F Γ a} → Env F Γ → Ref Γ a → F a
(x ∷ env) ! top      = x
(x ∷ env) ! pop ref  = env ! ref
