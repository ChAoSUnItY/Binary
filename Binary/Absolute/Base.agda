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


-- Computes |x - y| treating inputs as unsigned integers.
-- If x >= y, returns x - y.
-- If x < y, returns y - x.
-- This guarantees the result corresponds to the magnitude of the difference
-- without modular wrap-around affecting the interpretation (provided |x-y| < 2^(n+1)),
-- effectively essentially performing subtraction in ℕ lifted to Binary.
abs-sub : ∀ {n} (xs ys : Binary (suc n)) → Binary (suc n)
abs-sub {n} xs ys with trichotomyᵘ xs ys
... | tri-lt _ = ys - xs
... | tri-eq _ = zero (suc n)
... | tri-gt _ = xs - ys
