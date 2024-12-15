module Bin.Properties where
  
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Vec using (Vec; _∷_; []; drop; take; splitAt; length)
open import Bin.Base using (Bit; O; I; Binary; negate; flip; inc; dec; ~_)

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
  x ∷ xs                             ∎

-- inc properties

-- inc dec properties
inc-dec-involution : ∀ {n} (xs : Binary n) → dec (inc xs) ≡ xs
inc-dec-involution [] = refl
inc-dec-involution (O ∷ xs) = refl 
inc-dec-involution (I ∷ xs) = begin
  dec (inc (I ∷ xs)) ≡⟨⟩
  dec (O ∷ inc xs)   ≡⟨⟩
  I ∷ dec (inc xs)   ≡⟨ cong (I ∷_) (inc-dec-involution xs) ⟩
  I ∷ xs             ∎

-- 2's complement properties
~≡inc-flip : ∀ {n} (xs : Binary n) → inc (flip xs) ≡ ~ xs
~≡inc-flip [] = refl
~≡inc-flip (x ∷ xs) = refl

~-involution : ∀ {n} (xs : Binary n) → ~ (~ xs) ≡ xs
~-involution [] = refl
~-involution (O ∷ xs) = begin
  ~ (~ (O ∷ xs))                 ≡⟨⟩
  ~ (inc (flip (O ∷ xs)))        ≡⟨⟩
  ~ (inc (I ∷ flip xs))          ≡⟨⟩
  ~ (O ∷ inc (flip xs))          ≡⟨⟩
  inc (flip (O ∷ inc (flip xs))) ≡⟨⟩
  inc (I ∷ flip (inc (flip xs))) ≡⟨⟩
  O ∷ inc (flip (inc (flip xs))) ≡⟨ cong (O ∷_) (~≡inc-flip (inc (flip xs))) ⟩
  O ∷ ~ (inc (flip xs))          ≡⟨ cong (λ xs → O ∷ ~ xs) (~≡inc-flip xs) ⟩
  O ∷ ~ (~ xs)                   ≡⟨ cong (O ∷_) (~-involution xs) ⟩
  O ∷ xs                         ∎
~-involution (I ∷ xs) = begin
  ~ (~ (I ∷ xs))           ≡⟨⟩
  ~ (inc (flip (I ∷ xs)))  ≡⟨⟩
  ~ (inc (O ∷ flip xs))    ≡⟨⟩
  ~ (I ∷ flip xs)          ≡⟨⟩
  inc (flip (I ∷ flip xs)) ≡⟨⟩
  inc (O ∷ flip (flip xs)) ≡⟨⟩
  I ∷ flip (flip xs)       ≡⟨ cong (I ∷_) (flip-involution xs) ⟩
  I ∷ xs                   ∎
  