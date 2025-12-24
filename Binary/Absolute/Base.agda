module Binary.Absolute.Base where

open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; _∷_; [])
open import Binary.Base
open import Binary.Comparison.Base
open import Binary.Comparison.Properties

abs : ∀ {n} (xs : Binary (suc n)) → Binary (suc n)
abs xs with signBit xs
... | O = xs
... | I = - xs

nabs : ∀ {n} (xs : Binary (suc n)) → Binary (suc n)
nabs xs with signBit xs
... | O = - xs
... | I = xs

-- Computes |x - y| within unsigned domain, without causing
-- any overflow.
abs-sub : ∀ {n} (xs ys : Binary (suc n)) → Binary (suc n)
abs-sub {n} xs ys with trichotomyᵘ xs ys
... | tri-lt _ = ys - xs
... | tri-eq _ = zero (suc n)
... | tri-gt _ = xs - ys
