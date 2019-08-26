module Transpiler.Translation.Stage1.Padding where

open import Data.Nat using (suc; _+_)
open import Data.Nat.Extras using (_⊔₂_; compare₂; lesseq; greater)
open import Data.Product using (_,_)

open import Transpiler.IntermediateLang.IntermediateLang

-- Padding for the left side of a _⊔_ indexed circuit
left-pad : ∀ {G Γ} a b → IL[ G ] Γ 0 a → IL[ G ] Γ 0 (a ⊔₂ b)
left-pad a b x with compare₂ a b
left-pad a            .(a + k) x | lesseq .a k  = x ∥ Grnd
left-pad .(b + suc k) b        x | greater .b k = x

-- Padding for the right side of a _⊔_ indexed circuit
right-pad : ∀ {G Γ} a b → IL[ G ] Γ 0 b → IL[ G ] Γ 0 (a ⊔₂ b)
right-pad a b y with compare₂ a b
right-pad a            .(a + k) x | lesseq .a k  = x
right-pad .(b + suc k) b        x | greater .b k = x ∥ Grnd
