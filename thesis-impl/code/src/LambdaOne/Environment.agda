module LambdaOne.Environment where

open import Data.PolyTypes using (Uₚ; Tₚ)

open import Data.Environment (Uₚ) hiding (Env) public
open import Data.Environment (Uₚ) using () renaming (Env to Env')

Env : Ctxt → Set
Env = Env' Tₚ
