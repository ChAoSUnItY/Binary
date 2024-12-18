module Bin.Properties where
  
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; subst; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; _∷_; []; drop; take; splitAt; length)
open import Data.Bool.Properties using (not-involutive;
                                        ∨-comm; ∨-assoc;
                                        ∧-comm; ∧-assoc;
                                        xor-same; xor-comm; xor-assoc; xor-identityʳ; xor-identityˡ)
open import Data.Product using (_×_)
open import Bin.Base using (Bit; O; I; not; _and_; _or_; _xor_; 
                            Binary; zeroᴮ; onesᴮ; inc; dec; -_; ~_; _&_; _∥_; _^_; _<<ᴸ1; _>>ᴸ1)

-- n-bit Binary properties 
-- ~ properties
~-onesᴮ≡zeroᴮ : ∀ {n} → ~ onesᴮ n ≡ zeroᴮ n
~-onesᴮ≡zeroᴮ {zero} = refl
~-onesᴮ≡zeroᴮ {(suc n)} = begin
  ~ onesᴮ (suc n) ≡⟨⟩
  O ∷ (~ onesᴮ n) ≡⟨ cong (O ∷_) ~-onesᴮ≡zeroᴮ ⟩
  O ∷ (zeroᴮ n)   ≡⟨⟩
  zeroᴮ (suc n)   ∎

~-involutive : ∀ {n} (xs : Binary n) → ~ (~ xs) ≡ xs
~-involutive [] = refl
~-involutive (x ∷ xs) rewrite not-involutive x | ~-involutive xs = refl

-- inc properties

-- inc dec properties
inc-dec-involutive : ∀ {n} (xs : Binary n) → dec (inc xs) ≡ xs
inc-dec-involutive [] = refl
inc-dec-involutive (O ∷ xs) = refl 
inc-dec-involutive (I ∷ xs) rewrite inc-dec-involutive xs = refl

-- TODO: Complete this proof by prove injective and surjective of -
-- 2's complement properties
negate≡inc-~ : ∀ {n} (xs : Binary n) → inc (~ xs) ≡ - xs
negate≡inc-~ [] = refl
negate≡inc-~ (x ∷ xs) = refl

negate-involutive : ∀ {n} (xs : Binary n) → - (- xs) ≡ xs
negate-involutive [] = refl
negate-involutive (O ∷ xs) = begin
  - (- (O ∷ xs))           ≡⟨⟩
  - (inc (~ (O ∷ xs)))     ≡⟨⟩
  - (inc (I ∷ ~ xs))       ≡⟨⟩
  - (O ∷ inc (~ xs))       ≡⟨⟩
  inc (~ (O ∷ inc (~ xs))) ≡⟨⟩
  inc (I ∷ ~ (inc (~ xs))) ≡⟨⟩
  O ∷ inc (~ (inc (~ xs))) ≡⟨ cong (O ∷_) (negate≡inc-~ (inc (~ xs))) ⟩
  O ∷ - (inc (~ xs))       ≡⟨ cong (λ xs → O ∷ - xs) (negate≡inc-~ xs) ⟩
  O ∷ - (- xs)             ≡⟨ cong (O ∷_) (negate-involutive xs) ⟩
  O ∷ xs                   ∎
negate-involutive (I ∷ xs) = begin
  - (- (I ∷ xs))       ≡⟨⟩
  - (inc (~ (I ∷ xs))) ≡⟨⟩
  - (inc (O ∷ ~ xs))   ≡⟨⟩
  - (I ∷ ~ xs)         ≡⟨⟩
  inc (~ (I ∷ ~ xs))   ≡⟨⟩
  inc (O ∷ ~ (~ xs))   ≡⟨⟩
  I ∷ ~ (~ xs)         ≡⟨ cong (I ∷_) (~-involutive xs) ⟩
  I ∷ xs               ∎

-- ∥ properties
∥-comm : ∀ {n} (xs ys : Binary n) → xs ∥ ys ≡ ys ∥ xs
∥-comm [] [] = refl
∥-comm (x ∷ xs) (y ∷ ys) rewrite ∨-comm x y | ∥-comm xs ys = refl

-- & properties
and-distrib-and : ∀ (x y z : Bit) → x and (y and z) ≡ (x and y) and (x and z)
and-distrib-and O y z = refl
and-distrib-and I y z = refl

&-comm : ∀ {n} (xs ys : Binary n) → xs & ys ≡ ys & xs
&-comm [] [] = refl
&-comm (x ∷ xs) (y ∷ ys) rewrite ∧-comm x y | &-comm xs ys = refl

&-assoc : ∀ {n} (xs ys zs : Binary n) → (xs & ys) & zs ≡ xs & (ys & zs)
&-assoc [] [] [] = refl
&-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) rewrite ∧-assoc x y z | &-assoc xs ys zs = refl

&-distrib-& : ∀ {n} (xs ys zs : Binary n) → xs & (ys & zs) ≡ (xs & ys) & (xs & zs)
&-distrib-& [] [] [] = refl
&-distrib-& (x ∷ xs) (y ∷ ys) (z ∷ zs) rewrite and-distrib-and x y z | &-distrib-& xs ys zs = refl

-- ^ properties
^-same : ∀ {n} (xs : Binary n) → xs ^ xs ≡ zeroᴮ n
^-same [] = refl
^-same (x ∷ xs) rewrite xor-same x | ^-same xs = refl

^-comm : ∀ {n} (xs ys : Binary n) → xs ^ ys ≡ ys ^ xs
^-comm [] [] = refl
^-comm (x ∷ xs) (y ∷ ys) rewrite xor-comm x y | ^-comm xs ys = refl

^-assoc : ∀ {n} (xs ys zs : Binary n) → (xs ^ ys) ^ zs ≡ xs ^ (ys ^ zs)
^-assoc [] [] [] = refl
^-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) rewrite xor-assoc x y z | ^-assoc xs ys zs = refl

^-identityʳ : ∀ {n} (xs : Binary n) → xs ^ zeroᴮ n ≡ xs
^-identityʳ [] = refl
^-identityʳ (x ∷ xs) rewrite xor-identityʳ x | ^-identityʳ xs = refl

^-identityˡ : ∀ {n} (xs : Binary n) → zeroᴮ n ^ xs ≡ xs
^-identityˡ [] = refl
^-identityˡ (x ∷ xs) rewrite xor-identityˡ x | ^-identityˡ xs = refl

^-involutive : ∀ {n} (xs ys : Binary n) → (xs ^ ys) ^ ys ≡ xs
^-involutive [] [] = refl
^-involutive {n} (x ∷ xs) (y ∷ ys) = begin
  ((x ∷ xs) ^ (y ∷ ys)) ^ (y ∷ ys) ≡⟨ ^-assoc (x ∷ xs) (y ∷ ys) (y ∷ ys) ⟩
  (x ∷ xs) ^ ((y ∷ ys) ^ (y ∷ ys)) ≡⟨ cong ((x ∷ xs) ^_) (^-same (y ∷ ys)) ⟩
  (x ∷ xs) ^ zeroᴮ n               ≡⟨ ^-identityʳ (x ∷ xs) ⟩
  x ∷ xs                           ∎

-- ~-& and ~-∥ properties (De Morgan's Law)

not-distrib-or : ∀ (x y : Bit) → not (x or y) ≡ (not x) and (not y)
not-distrib-or I y = refl
not-distrib-or O y = refl

not-distrib-and : ∀ (x y : Bit) → not (x and y) ≡ (not x) or (not y)
not-distrib-and I y = refl
not-distrib-and O y = refl

~-distrib-∥ : ∀ {n} (xs ys : Binary n) → ~ (xs ∥ ys) ≡ (~ xs) & (~ ys)
~-distrib-∥ [] [] = refl
~-distrib-∥ (x ∷ xs) (y ∷ ys) rewrite not-distrib-or x y | ~-distrib-∥ xs ys = refl

~-distrib-& : ∀ {n} (xs ys : Binary n) → ~ (xs & ys) ≡ (~ xs) ∥ (~ ys)
~-distrib-& [] [] = refl
~-distrib-& (x ∷ xs) (y ∷ ys) rewrite not-distrib-and x y | ~-distrib-& xs ys = refl
 