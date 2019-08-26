module Data.Product.Extras where

open import Data.Product

map× : {A B : Set} → (A → B) → A × A → B × B
map× f = map f f
