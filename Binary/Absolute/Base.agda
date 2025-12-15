module Binary.Absolute.Base where

open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; _∷_; [])
open import Binary.Base
open import Binary.Comparison.Base
open import Binary.Comparison.Properties

abs : ∀ {n} (xs : Binary (suc n)) → Binary (suc n)
abs xs with isNegative xs
... | O = xs
... | I = - xs

nabs : ∀ {n} (xs : Binary (suc n)) → Binary (suc n)
nabs xs with isNegative xs
... | O = - xs
... | I = xs

