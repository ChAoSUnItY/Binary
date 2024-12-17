module Bin.Properties where
  
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; subst; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; _∷_; []; drop; take; splitAt; length)
open import Data.Bool.Properties using (not-involutive; xor-same; xor-comm; xor-assoc; xor-identityʳ; xor-identityˡ)
open import Data.Product using (_×_)
open import Bin.Base using (Bit; O; I; _xor_; Binary; zeroᴮ; onesᴮ; not; flip; inc; dec; ~_; _^_)

-- n-bit Binary properties 
-- flip properties
flip-involutive : ∀ {n} (xs : Binary n) → flip (flip xs) ≡ xs
flip-involutive [] = refl
flip-involutive (x ∷ xs) = begin
  flip (flip (x ∷ xs))         ≡⟨⟩
  flip (not x ∷ flip xs)       ≡⟨⟩
  not (not x) ∷ flip (flip xs) ≡⟨ cong (_∷ flip (flip xs)) (not-involutive x) ⟩
  x ∷ flip (flip xs)           ≡⟨ cong (x ∷_) (flip-involutive xs) ⟩
  x ∷ xs                       ∎

-- inc properties

-- inc dec properties
inc-dec-involutive : ∀ {n} (xs : Binary n) → dec (inc xs) ≡ xs
inc-dec-involutive [] = refl
inc-dec-involutive (O ∷ xs) = refl 
inc-dec-involutive (I ∷ xs) = begin
  dec (inc (I ∷ xs)) ≡⟨⟩
  dec (O ∷ inc xs)   ≡⟨⟩
  I ∷ dec (inc xs)   ≡⟨ cong (I ∷_) (inc-dec-involutive xs) ⟩
  I ∷ xs             ∎

-- TODO: Complete this proof by prove injective and surjective of ~
-- 2's complement properties
~≡inc-flip : ∀ {n} (xs : Binary n) → inc (flip xs) ≡ ~ xs
~≡inc-flip [] = refl
~≡inc-flip (x ∷ xs) = refl

~-involutive : ∀ {n} (xs : Binary n) → ~ (~ xs) ≡ xs
~-involutive [] = refl
~-involutive (O ∷ xs) = begin
  ~ (~ (O ∷ xs))                 ≡⟨⟩
  ~ (inc (flip (O ∷ xs)))        ≡⟨⟩
  ~ (inc (I ∷ flip xs))          ≡⟨⟩
  ~ (O ∷ inc (flip xs))          ≡⟨⟩
  inc (flip (O ∷ inc (flip xs))) ≡⟨⟩
  inc (I ∷ flip (inc (flip xs))) ≡⟨⟩
  O ∷ inc (flip (inc (flip xs))) ≡⟨ cong (O ∷_) (~≡inc-flip (inc (flip xs))) ⟩
  O ∷ ~ (inc (flip xs))          ≡⟨ cong (λ xs → O ∷ ~ xs) (~≡inc-flip xs) ⟩
  O ∷ ~ (~ xs)                   ≡⟨ cong (O ∷_) (~-involutive xs) ⟩
  O ∷ xs                         ∎
~-involutive (I ∷ xs) = begin
  ~ (~ (I ∷ xs))           ≡⟨⟩
  ~ (inc (flip (I ∷ xs)))  ≡⟨⟩
  ~ (inc (O ∷ flip xs))    ≡⟨⟩
  ~ (I ∷ flip xs)          ≡⟨⟩
  inc (flip (I ∷ flip xs)) ≡⟨⟩
  inc (O ∷ flip (flip xs)) ≡⟨⟩
  I ∷ flip (flip xs)       ≡⟨ cong (I ∷_) (flip-involutive xs) ⟩
  I ∷ xs                   ∎

-- ^ properties
^-same : ∀ {n} (xs : Binary n) → xs ^ xs ≡ zeroᴮ n
^-same [] = refl
^-same {(suc n)} (x ∷ xs) = begin
  (x ∷ xs) ^ (x ∷ xs)   ≡⟨⟩
  (x xor x) ∷ (xs ^ xs) ≡⟨ cong ((x xor x) ∷_) (^-same xs) ⟩
  (x xor x) ∷ zeroᴮ n   ≡⟨ cong (_∷ zeroᴮ n) (xor-same x) ⟩
  zeroᴮ (suc n)         ∎

^-comm : ∀ {n} (xs ys : Binary n) → xs ^ ys ≡ ys ^ xs
^-comm [] [] = refl
^-comm (x ∷ xs) (y ∷ ys) = begin
  (x ∷ xs) ^ (y ∷ ys)   ≡⟨⟩
  (x xor y) ∷ (xs ^ ys) ≡⟨ cong (_∷ (xs ^ ys)) (xor-comm x y) ⟩
  (y xor x) ∷ (xs ^ ys) ≡⟨ cong ((y xor x) ∷_) (^-comm xs ys) ⟩
  (y xor x) ∷ (ys ^ xs) ≡⟨⟩
  (y ∷ ys) ^ (x ∷ xs)   ∎

^-assoc : ∀ {n} (xs ys zs : Binary n) → (xs ^ ys) ^ zs ≡ xs ^ (ys ^ zs)
^-assoc [] [] [] = refl
^-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = begin
  ((x ∷ xs) ^ (y ∷ ys)) ^ (z ∷ zs)     ≡⟨⟩
  ((x xor y) ∷ (xs ^ ys)) ^ (z ∷ zs)   ≡⟨⟩
  ((x xor y) xor z) ∷ ((xs ^ ys) ^ zs) ≡⟨ cong (((x xor y) xor z) ∷_) (^-assoc xs ys zs) ⟩
  ((x xor y) xor z) ∷ (xs ^ (ys ^ zs)) ≡⟨ cong (_∷ (xs ^ (ys ^ zs))) (xor-assoc x y z) ⟩
  (x xor (y xor z)) ∷ (xs ^ (ys ^ zs)) ≡⟨⟩
  (x ∷ xs) ^ ((y ∷ ys) ^ (z ∷ zs))     ∎

^-identityʳ : ∀ {n} (xs : Binary n) → xs ^ zeroᴮ n ≡ xs
^-identityʳ [] = refl
^-identityʳ {(suc n)} (x ∷ xs) = begin
  (x ∷ xs) ^ zeroᴮ (suc n)   ≡⟨⟩
  (x xor O) ∷ (xs ^ zeroᴮ n) ≡⟨ cong ((x xor O) ∷_) (^-identityʳ xs) ⟩
  (x xor O) ∷ xs             ≡⟨ cong (_∷ xs) (xor-identityʳ x) ⟩
  x ∷ xs                     ∎

^-identityˡ : ∀ {n} (xs : Binary n) → zeroᴮ n ^ xs ≡ xs
^-identityˡ [] = refl
^-identityˡ {(suc n)} (x ∷ xs) = begin
  zeroᴮ (suc n) ^ (x ∷ xs)   ≡⟨⟩
  (O xor x) ∷ (zeroᴮ n ^ xs) ≡⟨ cong ((O xor x) ∷_) (^-identityˡ xs) ⟩
  (O xor x) ∷ xs             ≡⟨ cong (_∷ xs) (xor-identityˡ x) ⟩
  x ∷ xs ∎

^-involutive : ∀ {n} (xs ys : Binary n) → (xs ^ ys) ^ ys ≡ xs
^-involutive [] [] = refl
^-involutive {n} (x ∷ xs) (y ∷ ys) = begin
  ((x ∷ xs) ^ (y ∷ ys)) ^ (y ∷ ys) ≡⟨ ^-assoc (x ∷ xs) (y ∷ ys) (y ∷ ys) ⟩
  (x ∷ xs) ^ ((y ∷ ys) ^ (y ∷ ys)) ≡⟨ cong ((x ∷ xs) ^_) (^-same (y ∷ ys)) ⟩
  (x ∷ xs) ^ zeroᴮ n               ≡⟨ ^-identityʳ (x ∷ xs) ⟩
  x ∷ xs                           ∎
 