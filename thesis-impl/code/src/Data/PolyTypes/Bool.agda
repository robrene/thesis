module Data.PolyTypes.Bool where

open import Data.PolyTypes public

open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)

infixr 6 _∧_
infixr 5 _∨_ _xor_
infix  0 if_then_else_

Bool : Set
Bool = Tₚ 𝟚

pattern false = inj₁ ⊤.tt
pattern true  = inj₂ ⊤.tt

not : Bool → Bool
not true  = false
not false = true

if_then_else_ : ∀ {A : Uₚ} → Bool → Tₚ A → Tₚ A → Tₚ A
if true  then x else _ = x
if false then _ else y = y

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

_∨_ : Bool → Bool → Bool
true  ∨ b = true
false ∨ b = b

_xor_ : Bool → Bool → Bool
true  xor b = not b
false xor b = b
