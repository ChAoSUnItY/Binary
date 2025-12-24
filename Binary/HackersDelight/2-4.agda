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
open import Binary.AddProperties
open import Binary.Comparison.Base
open import Binary.Comparison.Properties
open import Binary.Properties
open import Binary.DozMinMax.Base
open import Binary.DozMinMax.Properties
open import Binary.Absolute.Base

open import Binary.HackersDelight.2-1

abs-eq-a : ∀ {n} (xs : Binary (suc n)) → abs xs ≡ (xs ^ (xs >>ˢ n)) - (xs >>ˢ n)
abs-eq-a {n} xs rewrite >>ˢ-signbit xs with signBit xs
... | O rewrite ^-identityʳ xs | nneg-zero≡zero {n} | +-identityʳ xs = refl
... | I rewrite ^-onesʳ xs 
              | nneg-ones≡inc-zero {suc n} 
              | sym (rca-inc-comm (~ xs) (zero (suc n)) O)
              | +-identityʳ (- xs)
              = refl

abs-eq-b : ∀ {n} (xs : Binary (suc n)) → abs xs ≡ (xs + (xs >>ˢ n)) ^ (xs >>ˢ n)
abs-eq-b {n} xs rewrite >>ˢ-signbit xs with signBit xs
... | O rewrite +-identityʳ xs | ^-identityʳ xs = refl
... | I rewrite +-ones≡dec xs | ^-onesʳ (dec xs) | ~-dec≡inc-~ xs = refl

abs-eq-c : ∀ {n} (xs : Binary (suc n)) → abs xs ≡ xs - ((xs + xs) & (xs >>ˢ n))
abs-eq-c {n} xs rewrite >>ˢ-signbit xs with signBit xs
... | O rewrite &-zeroʳ (xs + xs) | nneg-zero≡zero {n} | +-identityʳ xs = refl
... | I rewrite &-identityʳ (xs + xs)
              | nneg-distrib xs xs
              | sym (+-assoc xs (- xs) (- xs))
              | +-elimʳ xs
              | +-identityˡ (- xs) 
              = refl

nabs-eq-a : ∀ {n} (xs : Binary (suc n)) → nabs xs ≡ (xs >>ˢ n) - (xs ^ (xs >>ˢ n))
nabs-eq-a {n} xs rewrite >>ˢ-signbit xs with signBit xs
... | O rewrite ^-identityʳ xs | +-identityˡ (- xs) = refl
... | I rewrite ^-onesʳ xs 
              | ~-involutive xs
              | +-comm (ones (suc n)) (inc xs) 
              | +-ones≡dec (inc xs)
              | dec-inc-elim xs
              = refl

nabs-eq-b : ∀ {n} (xs : Binary (suc n)) → nabs xs ≡ ((xs >>ˢ n) - xs) ^ (xs >>ˢ n)
nabs-eq-b {n} xs rewrite >>ˢ-signbit xs with signBit xs
... | O rewrite +-identityˡ (- xs) | ^-identityʳ (- xs) = refl
... | I rewrite +-comm (ones (suc n)) (- xs)
              | +-ones≡dec (- xs)
              | dec-inc-elim (~ xs)
              | ^-onesʳ (~ xs)
              | ~-involutive xs 
              = refl

nabs-eq-c : ∀ {n} (xs : Binary (suc n)) → nabs xs ≡ ((xs + xs) & (xs >>ˢ n)) - xs
nabs-eq-c {n} xs rewrite >>ˢ-signbit xs with signBit xs
... | O rewrite &-zeroʳ (xs + xs) | +-identityˡ (- xs) = refl
... | I rewrite &-identityʳ (xs + xs)
              | +-assoc xs xs (- xs) 
              | +-elimʳ xs 
              | +-identityʳ xs
              = refl
