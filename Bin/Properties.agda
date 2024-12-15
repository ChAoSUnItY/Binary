module Bin.Properties where
  
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Vec using (Vec; _∷_; []; drop; take; splitAt; length)
open import Bin.Base using (Bit; O; I; Binary; negate; flip; inc; dec; twoComplement)

-- negate properties
negate-involution : ∀ (x : Bit) → negate (negate x) ≡ x
negate-involution O = refl
negate-involution I = refl

-- flip properties
flip-involution : ∀ {n} (xs : Binary n) → flip (flip xs) ≡ xs
flip-involution [] = refl
flip-involution (x ∷ xs) = begin
  flip (flip (x ∷ xs))               ≡⟨⟩
  flip (negate x ∷ flip xs)          ≡⟨⟩
  negate (negate x) ∷ flip (flip xs) ≡⟨ cong (_∷ flip (flip xs)) (negate-involution x) ⟩
  x ∷ flip (flip xs)                 ≡⟨ cong (x ∷_) (flip-involution xs) ⟩
  x ∷ xs ∎

-- inc properties

-- inc dec properties
inc-dec-involution : ∀ {n} (xs : Binary n) → dec (inc xs) ≡ xs
inc-dec-involution [] = refl
inc-dec-involution (O ∷ xs) = refl 
inc-dec-involution (I ∷ xs) = begin
  dec (inc (I ∷ xs)) ≡⟨⟩
  dec (O ∷ inc xs)   ≡⟨⟩
  I ∷ dec (inc xs)   ≡⟨ cong (I ∷_) (inc-dec-involution xs) ⟩
  I ∷ xs ∎

-- 2's complement properties
twoComplement≡inc-flip : ∀ {n} (xs : Binary n) → inc (flip xs) ≡ twoComplement xs
twoComplement≡inc-flip [] = refl
twoComplement≡inc-flip (x ∷ xs) = refl

twoComplement-involution : ∀ {n} (xs : Binary n) → twoComplement (twoComplement xs) ≡ xs
twoComplement-involution [] = refl
twoComplement-involution (O ∷ xs) = begin
  twoComplement (twoComplement (O ∷ xs)) ≡⟨⟩
  twoComplement (inc (flip (O ∷ xs)))    ≡⟨⟩
  twoComplement (inc (I ∷ flip xs))      ≡⟨⟩
  twoComplement (O ∷ inc (flip xs))      ≡⟨⟩
  inc (flip (O ∷ inc (flip xs)))         ≡⟨⟩
  inc (I ∷ flip (inc (flip xs)))         ≡⟨⟩
  O ∷ inc (flip (inc (flip xs)))         ≡⟨ cong (O ∷_) (twoComplement≡inc-flip (inc (flip xs))) ⟩
  O ∷ twoComplement (inc (flip xs))      ≡⟨ cong (λ xs → O ∷ twoComplement xs) (twoComplement≡inc-flip xs) ⟩
  O ∷ twoComplement (twoComplement xs)   ≡⟨ cong (O ∷_) (twoComplement-involution xs) ⟩
  O ∷ xs                                 ∎
twoComplement-involution (I ∷ xs) = begin
  twoComplement (twoComplement (I ∷ xs)) ≡⟨⟩
  twoComplement (inc (flip (I ∷ xs)))    ≡⟨⟩
  twoComplement (inc (O ∷ flip xs))      ≡⟨⟩
  twoComplement (I ∷ flip xs)            ≡⟨⟩
  inc (flip (I ∷ flip xs))               ≡⟨⟩
  inc (O ∷ flip (flip xs))               ≡⟨⟩
  I ∷ flip (flip xs)                     ≡⟨ cong (I ∷_) (flip-involution xs) ⟩
  I ∷ xs ∎
  