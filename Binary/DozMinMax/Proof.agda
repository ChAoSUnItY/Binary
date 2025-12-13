module Binary.DozMinMax.Proof where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; _∷_; [])
open import Binary.Base
open import Binary.Comparison.Base
open import Binary.Comparison.Properties
open import Binary.Properties
open import Binary.DozMinMax.Base
open import Binary.DozMinMax.Properties
open import Binary.AddProperties

∥-≥ᵘ-maxᵘ : ∀ {n} (xs ys : Binary (suc n)) → (xs ∥ ys) ≥ᵘ maxᵘ xs ys
∥-≥ᵘ-maxᵘ xs ys with trichotomy xs ys
... | tri-lt _ = ∥-≥ᵘ-right
... | tri-eq _ = ∥-≥ᵘ-left
... | tri-gt _ = ∥-≥ᵘ-left

&-≤ᵘ-minᵘ : ∀ {n} (xs ys : Binary (suc n)) → (xs & ys) ≤ᵘ minᵘ xs ys
&-≤ᵘ-minᵘ xs ys with trichotomy xs ys
... | tri-lt _ = &-≤ᵘ-left
... | tri-eq _ = &-≤ᵘ-right
... | tri-gt _ = &-≤ᵘ-right
