module Transpiler.IntermediateLang.Plugs where

open import Function using (_$_)
open import Data.Fin using (inject+)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_; _×_; uncurry)
open import Data.Vec using ([]; _++_; allFin; splitAt; tabulate)
open import Data.Vec.Extras using (_⇇_; split|n+n|)

open import Transpiler.IntermediateLang.IntermediateLang using (IL[_]; Plug)

⇇-id : ∀ n → n ⇇ n
⇇-id n = allFin n

PlugId : ∀ {G Γ} n → IL[ G ] Γ n n
PlugId n = Plug $ ⇇-id n

PlugId' : ∀ {G Γ n} → IL[ G ] Γ n n
PlugId' {n = n} = PlugId n

⇇-nil : ∀ n → n ⇇ 0
⇇-nil n = []

PlugNil : ∀ {G Γ} n → IL[ G ] Γ n 0
PlugNil n = Plug $ ⇇-nil n

⇇-dup : ∀ n → n ⇇ (n + n)
⇇-dup n = ⇇-id n ++ ⇇-id n

PlugDup : ∀ {G Γ} n → IL[ G ] Γ n (n + n)
PlugDup n = Plug $ ⇇-dup n

⇇-copyk : ∀ n k → (k + n) ⇇ (k + n + k)
⇇-copyk n k = ⇇-id (k + n) ++ tabulate (inject+ n)

PlugCopyK : ∀ {G Γ} n k → IL[ G ] Γ (k + n) (k + n + k)
PlugCopyK n k = Plug $ ⇇-copyk n k

⇇-flip : ∀ n k → (n + k) ⇇ (k + n)
⇇-flip n k with splitAt n (⇇-id (n + k))
⇇-flip n k | ns , ks , _ = ks ++ ns

PlugFlip : ∀ {G Γ} n k → IL[ G ] Γ (n + k) (k + n)
PlugFlip n k = Plug $ ⇇-flip n k
