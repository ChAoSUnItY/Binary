module Binary.DozMinMax.Base where

open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; _∷_; [])
open import Binary.Base
open import Binary.Comparison.Base
open import Binary.Comparison.Properties

dozᵘ : ∀ {n} (xs ys : Binary (suc n)) → Binary (suc n)
dozᵘ {n} xs ys with trichotomyᵘ xs ys
... | tri-lt lth = zero (suc n)
... | _ = xs - ys

maxᵘ : ∀ {n} (xs ys : Binary (suc n)) → Binary (suc n)
maxᵘ {n} xs ys with trichotomyᵘ xs ys
... | tri-lt lth = ys
... | _ = xs

minᵘ : ∀ {n} (xs ys : Binary (suc n)) → Binary (suc n)
minᵘ {n} xs ys with trichotomyᵘ xs ys
... | tri-lt lth = xs
... | _ = ys

