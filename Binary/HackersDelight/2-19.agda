module Binary.HackersDelight.2-19 where

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
open import Binary.AddProperties
open import Binary.Comparison.Base
open import Binary.Comparison.Properties
open import Binary.Properties
open import Binary.DozMinMax.Base
open import Binary.DozMinMax.Properties
open import Binary.Absolute.Base

maxᵘ≡+-dozᵘ : ∀ {n} (xs ys : Binary (suc n)) → maxᵘ xs ys ≡ (ys + dozᵘ xs ys)
maxᵘ≡+-dozᵘ {n} xs ys with trichotomyᵘ xs ys
... | tri-lt _ rewrite +-identityʳ ys = refl
... | tri-eq eq rewrite eq | +-elimʳ ys | +-identityʳ ys = refl
... | tri-gt _ rewrite +-comm xs (- ys) 
                     | sym (+-assoc ys (- ys) xs) 
                     | +-elimʳ ys 
                     | +-identityˡ xs
                     = refl

minᵘ≡sub-dozᵘ : ∀ {n} (xs ys : Binary (suc n)) → minᵘ xs ys ≡ (xs - dozᵘ xs ys)
minᵘ≡sub-dozᵘ {n} xs ys with trichotomyᵘ xs ys
... | tri-lt _ rewrite nneg-zero≡zero {n} | +-identityʳ xs = refl
... | tri-eq eq rewrite eq 
                      | +-elimʳ ys 
                      | nneg-zero≡zero {n} 
                      | +-identityʳ ys 
                      = refl
... | tri-gt _ rewrite nneg-distrib xs (- ys)
                     | nneg-involutive ys 
                     | sym (+-assoc xs (- xs) ys)
                     | +-elimʳ xs
                     | +-identityˡ ys
                     = refl
