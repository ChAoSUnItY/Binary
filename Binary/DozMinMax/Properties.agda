module Binary.DozMinMax.Properties where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; _∷_; [])
open import Binary.Base
open import Binary.Comparison.Base
open import Binary.Comparison.Properties
open import Binary.DozMinMax.Base
open import Binary.AddProperties

dozᵘ-⌊⌋ : ∀ {n} (xs ys : Binary (suc n)) → zero (suc n) ≤ᵘ dozᵘ xs ys
dozᵘ-⌊⌋ {n} xs ys with trichotomyᵘ xs ys
... | tri-lt lth = inj₂ refl
... | tri-eq refl rewrite +-elimʳ xs = inj₂ refl
... | tri-gt gth = zero-≤ᵘ-all _

dozᵘ-⌈⌉ : ∀ {n} (xs ys : Binary (suc n)) → dozᵘ xs ys ≤ᵘ maxᵘ xs ys
dozᵘ-⌈⌉ {n} xs ys with trichotomyᵘ xs ys
... | tri-lt lth = zero-≤ᵘ-all ys
... | tri-eq refl rewrite +-elimʳ xs = zero-≤ᵘ-all xs
... | tri-gt gth = sub-<ᵘ-self gth
