module PiWare.Gates where

open import Data.Nat using (ℕ)

record Gates : Set₁ where
  field  Gate#     : Set
         #in #out  : Gate# → ℕ

open Gates public
