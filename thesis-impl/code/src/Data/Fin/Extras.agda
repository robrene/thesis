module Data.Fin.Extras where

open import Data.Fin
open import Data.Nat renaming (_+_ to _ℕ+_)

-- From [Generic Programming with Dependent Types] by Altenkirch, McBride & Morris:

-- Map the elements of Fin m to the first m elements of Fin (m ℕ+ n)
finl : (m n : ℕ) → (i : Fin m) → Fin (m ℕ+ n)
finl zero n ()
finl (suc m) n zero     = zero
finl (suc m) n (suc i)  = suc (finl m n i)

-- Map the elements of Fin n to the subsequent n elements of Fin (m ℕ+ n)
finr : (m n : ℕ) → (i : Fin n) → Fin (m ℕ+ n)
finr zero n i     = i
finr (suc m) n i  = suc (finr m n i)

-- An alternative view/covering of the type family Fin (m ℕ+ n)
data FinPlus (m n : ℕ) : Fin (m ℕ+ n) → Set where
  isfinl : (i : Fin m) → FinPlus m n (finl m n i)
  isfinr : (i : Fin n) → FinPlus m n (finr m n i)

-- Exhaustive coverage for the FinPlus view
finPlus : (m n : ℕ) → (i : Fin (m ℕ+ n)) → FinPlus m n i
finPlus zero n i = isfinr i
finPlus (suc m) n zero = isfinl zero
finPlus (suc m) n (suc i) with finPlus m n i
finPlus (suc m) n (suc .(finl m n i)) | isfinl i = isfinl (suc i)
finPlus (suc m) n (suc .(finr m n i)) | isfinr i = isfinr i
