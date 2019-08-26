module Transpiler.Translation.Stage1.CombinatorCircuits where

open import Function using (_$_)
open import Data.Nat using (_+_)
open import Data.Nat.Properties using (+-assoc)
open import Relation.Binary.PropositionalEquality using (sym)

open import Transpiler.IntermediateLang.Coerce
open import Transpiler.IntermediateLang.IntermediateLang
open import Transpiler.IntermediateLang.Plugs

-- K[ k ]· x
--
--          Nil
--           ∥
--           x
--
--    k -----!
--        |`````|
--    i --|  x  |-- o
--        |_____|

K[_]·_ : ∀ {G Γ i o} k → IL[ G ] Γ i o → IL[ G ] Γ (k + i) o
K[ k ]· x = PlugNil k ∥ x

-- S[ k ]· x · y
--
--       Dup         Id
--        ∥    ⟫     ∥      ⟫      y
--        Id         x
--
--        ,-- k ----------- k --|`````|
--    k --+-- k --|`````|       |  y  |-- o
--                |  x  |-- j --|_____|
--    i ----- i --|_____|

S-bypass : ∀ {G Γ} k i → IL[ G ] Γ (k + i) (k + (k + i))
S-bypass k i = coerceₒ (+-assoc k k i) $ PlugDup k ∥ PlugId i

S[_]·_·_ : ∀ {G Γ i j o} k → IL[ G ] Γ (k + i) j → IL[ G ] Γ (k + j) o → IL[ G ] Γ (k + i) o
S[_]·_·_ {i = i} k x y = S-bypass k i ⟫ PlugId k ∥ x ⟫ y

-- P[ k ]· x · y
--
--       CopyK        x
--         ∥    ⟫     ∥
--         Id         y
--
--    k ---+-- k --|`````|
--         |       |  x  |-- o₁
--    i₁ - | - i₁ -|_____|
--         |
--         `-- k --|`````|
--                 |  y  |-- o₂
--    i₂ ----- i₂ -|_____|

P-insert : ∀ {G Γ} k i₁ i₂ → IL[ G ] Γ (k + (i₁ + i₂)) ((k + i₁) + (k + i₂))
P-insert k i₁ i₂ = coerceᵢₒ (+-assoc k i₁ i₂) (+-assoc (k + i₁) k i₂) $ PlugCopyK i₁ k ∥ PlugId i₂

P[_]·_·_ : ∀ {G Γ i₁ o₁ i₂ o₂} k → IL[ G ] Γ (k + i₁) o₁ → IL[ G ] Γ (k + i₂) o₂ → IL[ G ] Γ (k + (i₁ + i₂)) (o₁ + o₂)
P[_]·_·_ {i₁ = i₁} {i₂ = i₂} k x y = P-insert k i₁ i₂ ⟫ x ∥ y
