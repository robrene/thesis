module PiWare.Gates.BoolTrio where

open import Data.Nat using (ℕ)
open import PiWare.Gates public

data BoolTrioGate : Set where
  ℂ-true ℂ-false ℂ-not ℂ-and ℂ-or : BoolTrioGate

booltrio-input : BoolTrioGate → ℕ
booltrio-input ℂ-true   = 0
booltrio-input ℂ-false  = 0
booltrio-input ℂ-not    = 1
booltrio-input ℂ-and    = 2
booltrio-input ℂ-or     = 2

booltrio-output : BoolTrioGate → ℕ
booltrio-output ℂ-true   = 1
booltrio-output ℂ-false  = 1
booltrio-output ℂ-not    = 1
booltrio-output ℂ-and    = 1
booltrio-output ℂ-or     = 1

BoolTrio : Gates
BoolTrio = record  { Gate#  = BoolTrioGate
                   ; #in    = booltrio-input
                   ; #out   = booltrio-output
                   }
