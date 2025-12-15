module Binary.HackersDelight.2-4 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; cong-app; subst; trans; sym)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Vec using (Vec; _∷_; []; map; foldl)
open import Data.Vec.Properties
open import Data.Nat using (ℕ; suc)
open import Data.Bool using (_∧_; _∨_; not; _xor_)
open import Data.Bool.Properties
open import Function.Base
open import Binary.Base
open import Binary.Comparison.Base
open import Binary.Comparison.Properties
open import Binary.Properties
open import Binary.DozMinMax.Base
open import Binary.DozMinMax.Properties
open import Binary.Absolute.Base
open import Binary.AddProperties

abs-eq-a : ∀ {n} (xs : Binary (suc n)) → abs xs ≡ (xs ^ (xs >>ˢ n)) - (xs >>ˢ n)
abs-eq-a xs with signBit xs
... | O = {!    !}
... | I = {!    !}
