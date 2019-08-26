module Data.Nat.Extras where

open import Data.Nat hiding (_⊔_; Ordering; less; equal; greater; compare)
import Level using (zero)
open import Relation.Binary

data Ordering : Rel ℕ Level.zero where
  less    : ∀ m k → Ordering m (m + suc k)
  equal   : ∀ m   → Ordering m m
  greater : ∀ m k → Ordering (m + suc k) m

compare : ∀ m n → Ordering m n
compare zero    zero    = equal   zero
compare (suc m) zero    = greater zero m
compare zero    (suc n) = less    zero n
compare (suc m) (suc n) with compare m n
compare (suc m)            (suc .(m + suc k)) | less .m k    = less    (suc m) k
compare (suc m)            (suc .m)           | equal .m     = equal   (suc m)
compare (suc .(n + suc k)) (suc n)            | greater .n k = greater (suc n) k

_⊔_ : ℕ → ℕ → ℕ
m ⊔ n with compare m n
m            ⊔ .(m + suc k) | less .m k    = m + suc k
m            ⊔ .m           | equal .m     = m
.(n + suc k) ⊔ n            | greater .n k = n + suc k

data Ordering₂ : Rel ℕ Level.zero where
  lesseq  : ∀ m k → Ordering₂ m (m + k)
  greater : ∀ m k → Ordering₂ (m + suc k) m

compare₂ : ∀ m n → Ordering₂ m n
compare₂ zero    n    = lesseq zero n
compare₂ (suc m) zero = greater zero m
compare₂ (suc m) (suc n) with compare₂ m n
compare₂ (suc m)            (suc .(m + k)) | lesseq .m k  = lesseq (suc m) k
compare₂ (suc .(n + suc k)) (suc n)        | greater .n k = greater (suc n) k

_⊔₂_ : ℕ → ℕ → ℕ
m ⊔₂ n with compare₂ m n
m            ⊔₂ .(m + k) | lesseq .m k  = m + k
.(n + suc k) ⊔₂ n        | greater .n k = n + suc k

_·2 : ℕ → ℕ
zero  ·2  = zero
suc n ·2  = (1 + 1) + n ·2
