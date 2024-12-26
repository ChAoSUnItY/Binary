module Bin.Properties where
  
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; cong-app; subst; trans; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; _∷_; []; drop; take; splitAt; length; head)
open import Data.Bool using (_∧_; _∨_; not; _xor_; T)
open import Data.Bool.Properties using (not-involutive;
                                        ∨-comm; ∨-assoc; ∨-identityʳ; ∨-zeroʳ;
                                        ∧-comm; ∧-assoc; ∧-zeroˡ; ∧-zeroʳ; ∧-distribʳ-xor; ∧-identityʳ; ∧-identityˡ;
                                        true-xor; xor-same; xor-comm; xor-assoc; xor-identityʳ; xor-identityˡ; ∧-distribˡ-xor; not-distribʳ-xor)
open import Bin.Base using (Bit; O; I;
                            Binary; zeroᴮ; onesᴮ; inc; dec; -_; ~_; _&_; _∥_; _^_; _<<ᴸ1; _>>ᴸ1; _+_; _-_;
                            rca)

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
and-distrib-and : ∀ (x y z : Bit) → x ∧ (y ∧ z) ≡ (x ∧ y) ∧ (x ∧ z)
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
false-xorˡ : (x : Bit) → O xor x ≡ x
false-xorˡ O = refl
false-xorˡ I = refl

false-xorʳ : (x : Bit) → x xor O ≡ x
false-xorʳ O = refl
false-xorʳ I = refl

true-xorʳ : (x : Bit) → x xor I ≡ not x
true-xorʳ O = refl
true-xorʳ I = refl

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

not-distrib-∨ : ∀ (x y : Bit) → not (x ∨ y) ≡ (not x) ∧ (not y)
not-distrib-∨ I y = refl
not-distrib-∨ O y = refl

not-distrib-and : ∀ (x y : Bit) → not (x ∧ y) ≡ (not x) ∨ (not y)
not-distrib-and I y = refl
not-distrib-and O y = refl

~-distrib-∥ : ∀ {n} (xs ys : Binary n) → ~ (xs ∥ ys) ≡ (~ xs) & (~ ys)
~-distrib-∥ [] [] = refl
~-distrib-∥ (x ∷ xs) (y ∷ ys) rewrite not-distrib-∨ x y | ~-distrib-∥ xs ys = refl

~-distrib-& : ∀ {n} (xs ys : Binary n) → ~ (xs & ys) ≡ (~ xs) ∥ (~ ys)
~-distrib-& [] [] = refl
~-distrib-& (x ∷ xs) (y ∷ ys) rewrite not-distrib-and x y | ~-distrib-& xs ys = refl

-- add / sub properties
rca-no-carry : ∀ {n} (x : Bit) (xs : Binary n) (y : Bit) (ys : Binary n) → rca (x ∷ xs) (y ∷ ys) O ≡ (x xor y) ∷ rca xs ys (x ∧ y)
rca-no-carry O [] O [] = refl
rca-no-carry x xs y ys = begin
    rca (x ∷ xs) (y ∷ ys) O ≡⟨⟩
  (x xor y xor O) ∷ rca xs ys ((x ∧ y) ∨ (O ∧ (x xor y))) 
    ≡⟨ cong (λ l → (x xor l) ∷ rca xs ys ((x ∧ y) ∨ (O ∧ (x xor y)))) (false-xorʳ y) ⟩
  (x xor y) ∷ rca xs ys ((x ∧ y) ∨ (O ∧ (x xor y))) 
    ≡⟨ cong (λ l → (x xor y) ∷ rca xs ys ((x ∧ y) ∨ l)) (∧-zeroˡ (x xor y)) ⟩
  (x xor y) ∷ rca xs ys ((x ∧ y) ∨ O) 
    ≡⟨ cong (λ l → (x xor y) ∷ rca xs ys l) (∨-identityʳ (x ∧ y)) ⟩
  (x xor y) ∷ rca xs ys (x ∧ y) 
    ∎

add-identityʳ : ∀ {n} (xs : Binary n) → xs + (zeroᴮ n) ≡ xs
add-identityʳ [] = refl
add-identityʳ {(suc n)} (x ∷ xs) = begin
  ((x ∷ xs) + zeroᴮ (suc n))           ≡⟨⟩
  (rca (x ∷ xs) (O ∷ zeroᴮ n) O)       ≡⟨ rca-no-carry x xs O (zeroᴮ n) ⟩
  (x xor O) ∷ rca xs (zeroᴮ n) (x ∧ O) ≡⟨ cong (_∷ rca xs (zeroᴮ n) (x ∧ O)) (false-xorʳ x) ⟩
  x ∷ rca xs (zeroᴮ n) (x ∧ O)         ≡⟨ cong (λ l → x ∷ rca xs (zeroᴮ n) l) (∧-zeroʳ x) ⟩
  x ∷ rca xs (zeroᴮ n) O               ≡⟨ cong (x ∷_) (add-identityʳ xs) ⟩
  x ∷ xs                               ∎

add-identityˡ : ∀ {n} (xs : Binary n) → (zeroᴮ n) + xs ≡ xs
add-identityˡ [] = refl
add-identityˡ {(suc n)} (x ∷ xs) = begin
  (zeroᴮ (suc n) + (x ∷ xs))           ≡⟨⟩
  (rca (O ∷ zeroᴮ n) (x ∷ xs) O)       ≡⟨ rca-no-carry O (zeroᴮ n) x xs ⟩
  (O xor x) ∷ rca (zeroᴮ n) xs (O ∧ x) ≡⟨ cong (_∷ rca (zeroᴮ n) xs (O ∧ x)) (false-xorˡ x) ⟩
  x ∷ rca (zeroᴮ n) xs (O ∧ x)         ≡⟨ cong (λ l → x ∷ rca (zeroᴮ n) xs l) (∧-zeroˡ x) ⟩
  x ∷ rca (zeroᴮ n) xs O               ≡⟨ cong (x ∷_) (add-identityˡ xs) ⟩
  x ∷ xs                               ∎

rca-comm : ∀ {n} {carry : Bit} (xs ys : Binary n) → rca xs ys carry ≡ rca ys xs carry
rca-comm [] [] = refl
rca-comm {suc n} {O} (O ∷ xs) (O ∷ ys) rewrite rca-comm {n} {O} xs ys = refl
rca-comm {suc n} {O} (O ∷ xs) (I ∷ ys) rewrite rca-comm {n} {O} xs ys = refl
rca-comm {suc n} {O} (I ∷ xs) (O ∷ ys) rewrite rca-comm {n} {O} xs ys = refl
rca-comm {suc n} {O} (I ∷ xs) (I ∷ ys) rewrite rca-comm {n} {I} xs ys = refl
rca-comm {suc n} {I} (O ∷ xs) (O ∷ ys) rewrite rca-comm {n} {O} xs ys = refl
rca-comm {suc n} {I} (O ∷ xs) (I ∷ ys) rewrite rca-comm {n} {I} xs ys = refl
rca-comm {suc n} {I} (I ∷ xs) (O ∷ ys) rewrite rca-comm {n} {I} xs ys = refl
rca-comm {suc n} {I} (I ∷ xs) (I ∷ ys) rewrite rca-comm {n} {I} xs ys = refl

rca-carry≡rca-incˡ : ∀ {n} (xs ys : Binary n) → rca xs ys I ≡ rca (inc xs) ys O
rca-carry≡rca-incˡ [] [] = refl
rca-carry≡rca-incˡ (O ∷ xs) (O ∷ ys) = refl
rca-carry≡rca-incˡ (O ∷ xs) (I ∷ ys) = refl
rca-carry≡rca-incˡ (I ∷ xs) (O ∷ ys) rewrite rca-carry≡rca-incˡ xs ys = refl
rca-carry≡rca-incˡ (I ∷ xs) (I ∷ ys) rewrite rca-carry≡rca-incˡ xs ys = refl

rca-carry≡rca-incʳ : ∀ {n} (xs ys : Binary n) → rca xs ys I ≡ rca xs (inc ys) O
rca-carry≡rca-incʳ [] [] = refl
rca-carry≡rca-incʳ (O ∷ xs) (O ∷ ys) = refl
rca-carry≡rca-incʳ (I ∷ xs) (O ∷ ys) = refl
rca-carry≡rca-incʳ (O ∷ xs) (I ∷ ys) rewrite rca-carry≡rca-incʳ xs ys = refl
rca-carry≡rca-incʳ (I ∷ xs) (I ∷ ys) rewrite rca-carry≡rca-incʳ xs ys = refl

rca-carry-comm : ∀ {n} {inner outer : Bit} (xs ys zs : Binary n) → rca (rca xs ys inner) zs outer ≡ rca (rca xs ys outer) zs inner
rca-carry-comm [] [] [] = refl
rca-carry-comm {suc n} {O} {O} _ _ _ = refl
rca-carry-comm {suc n} {I} {I} _ _ _ = refl
rca-carry-comm {suc n} {O} {I} (O ∷ xs) (O ∷ ys) (O ∷ zs) = refl
rca-carry-comm {suc n} {O} {I} (O ∷ xs) (O ∷ ys) (I ∷ zs) = refl
rca-carry-comm {suc n} {O} {I} (O ∷ xs) (I ∷ ys) (O ∷ zs) rewrite rca-carry-comm {n} {O} {I} xs ys zs = refl
rca-carry-comm {suc n} {O} {I} (O ∷ xs) (I ∷ ys) (I ∷ zs) rewrite rca-carry-comm {n} {O} {I} xs ys zs = refl
rca-carry-comm {suc n} {O} {I} (I ∷ xs) (O ∷ ys) (O ∷ zs) rewrite rca-carry-comm {n} {O} {I} xs ys zs = refl
rca-carry-comm {suc n} {O} {I} (I ∷ xs) (O ∷ ys) (I ∷ zs) rewrite rca-carry-comm {n} {O} {I} xs ys zs = refl
rca-carry-comm {suc n} {O} {I} (I ∷ xs) (I ∷ ys) (O ∷ zs) = refl
rca-carry-comm {suc n} {O} {I} (I ∷ xs) (I ∷ ys) (I ∷ zs) = refl
rca-carry-comm {suc n} {I} {O} (O ∷ xs) (O ∷ ys) (O ∷ zs) = refl
rca-carry-comm {suc n} {I} {O} (O ∷ xs) (O ∷ ys) (I ∷ zs) = refl
rca-carry-comm {suc n} {I} {O} (O ∷ xs) (I ∷ ys) (O ∷ zs) rewrite rca-carry-comm {n} {I} {O} xs ys zs = refl
rca-carry-comm {suc n} {I} {O} (O ∷ xs) (I ∷ ys) (I ∷ zs) rewrite rca-carry-comm {n} {I} {O} xs ys zs = refl
rca-carry-comm {suc n} {I} {O} (I ∷ xs) (O ∷ ys) (O ∷ zs) rewrite rca-carry-comm {n} {I} {O} xs ys zs = refl
rca-carry-comm {suc n} {I} {O} (I ∷ xs) (O ∷ ys) (I ∷ zs) rewrite rca-carry-comm {n} {I} {O} xs ys zs = refl
rca-carry-comm {suc n} {I} {O} (I ∷ xs) (I ∷ ys) (O ∷ zs) = refl
rca-carry-comm {suc n} {I} {O} (I ∷ xs) (I ∷ ys) (I ∷ zs) = refl

add-sub-involutive : ∀ {n} (xs ys : Binary n) → (xs - ys) + ys ≡ xs
add-sub-involutive [] [] = refl
add-sub-involutive (x ∷ xs) (O ∷ ys) = 
  begin
    (((x ∷ xs) - (O ∷ ys)) + (O ∷ ys)) 
  ≡⟨⟩
    rca (rca (x ∷ xs) (inc (I ∷ (~ ys))) O) (O ∷ ys) O
  ≡⟨⟩
    rca (rca (x ∷ xs) (O ∷ inc (~ ys)) O) (O ∷ ys) O
  ≡⟨ cong (λ l → rca l (O ∷ ys) O) (rca-no-carry x xs O (inc (~ ys))) ⟩
    rca ((x xor O) ∷ rca xs (inc (~ ys)) (x ∧ O)) (O ∷ ys) O
  ≡⟨ cong (λ l → rca (l ∷ rca xs (inc (~ ys)) (x ∧ O)) (O ∷ ys) O) (false-xorʳ x) ⟩
    rca (x ∷ rca xs (inc (~ ys)) (x ∧ O)) (O ∷ ys) O
  ≡⟨ cong (λ l → rca (x ∷ rca xs (inc (~ ys)) l) (O ∷ ys) O) (∧-zeroʳ x) ⟩
    rca (x ∷ rca xs (inc (~ ys)) O) (O ∷ ys) O
  ≡⟨ cong (λ l → rca (x ∷ rca xs l O) (O ∷ ys) O) (negate≡inc-~ ys) ⟩
    rca (x ∷ rca xs (- ys) O) (O ∷ ys) O 
  ≡⟨ rca-no-carry x (rca xs (- ys) O) O ys ⟩
    (x xor O) ∷ rca (rca xs (- ys) O) ys (x ∧ O)
  ≡⟨ cong (_∷ rca (rca xs (- ys) O) ys (x ∧ O)) (false-xorʳ x) ⟩
    x ∷ rca (rca xs (- ys) O) ys (x ∧ O)
  ≡⟨ cong (λ l → x ∷ rca (rca xs (- ys) O) ys l) (∧-zeroʳ x) ⟩
    x ∷ rca (rca xs (- ys) O) ys O
  ≡⟨ cong (x ∷_) (add-sub-involutive xs ys) ⟩
    x ∷ xs
  ∎
add-sub-involutive (O ∷ xs) (I ∷ ys) = 
  begin
    (((O ∷ xs) - (I ∷ ys)) + (I ∷ ys)) 
  ≡⟨⟩
    rca (rca (O ∷ xs) (inc (O ∷ (~ ys))) O) (I ∷ ys) O
  ≡⟨⟩
    rca (rca (O ∷ xs) (I ∷ (~ ys)) O) (I ∷ ys) O
  ≡⟨ cong (λ l → rca l (I ∷ ys) O) (rca-no-carry O xs I (~ ys)) ⟩
    rca ((O xor I) ∷ rca xs (~ ys) (O ∧ I)) (I ∷ ys) O
  ≡⟨ cong (λ l → rca (l ∷ rca xs (~ ys) (O ∧ I)) (I ∷ ys) O) (true-xorʳ O) ⟩
    rca (not O ∷ rca xs (~ ys) (O ∧ I)) (I ∷ ys) O
  ≡⟨ cong (λ l → rca (not O ∷ rca xs (~ ys) l) (I ∷ ys) O) (∧-identityʳ O) ⟩
    rca (not O ∷ rca xs (~ ys) O) (I ∷ ys) O
  ≡⟨ rca-no-carry (not O) (rca xs (~ ys) O) I ys ⟩
    (not O xor I) ∷ rca (rca xs (~ ys) O) ys (not O ∧ I)
  ≡⟨ cong (_∷ rca (rca xs (~ ys) O) ys (not O ∧ I)) (true-xorʳ (not O)) ⟩
    (not (not O)) ∷ rca (rca xs (~ ys) O) ys (not O ∧ I)
  ≡⟨ cong (_∷ rca (rca xs (~ ys) O) ys (not O ∧ I)) (not-involutive O) ⟩
    O ∷ rca (rca xs (~ ys) O) ys (not O ∧ I)
  ≡⟨ cong (λ l → O ∷ rca (rca xs (~ ys) O) ys l) (∧-identityʳ (not O)) ⟩
    O ∷ rca (rca xs (~ ys) O) ys (not O)
  ≡⟨⟩
    O ∷ rca (rca xs (~ ys) O) ys I
  ≡⟨ cong (O ∷_) (rca-carry-comm xs (~ ys) ys) ⟩
    O ∷ rca (rca xs (~ ys) I) ys O
  ≡⟨ cong (λ l → O ∷ rca l ys O) (rca-carry≡rca-incʳ xs (~ ys)) ⟩
    O ∷ rca (rca xs (inc (~ ys)) O) ys O
  ≡⟨ cong (λ l → O ∷ rca (rca xs l O) ys O) (negate≡inc-~ ys) ⟩
    O ∷ rca (rca xs (- ys) O) ys O
  ≡⟨ cong (O ∷_) (add-sub-involutive xs ys) ⟩
    O ∷ xs
  ∎
add-sub-involutive (I ∷ xs) (I ∷ ys) = 
  begin
    (((I ∷ xs) - (I ∷ ys)) + (I ∷ ys)) 
  ≡⟨⟩
    rca (rca (I ∷ xs) (inc (O ∷ (~ ys))) O) (I ∷ ys) O
  ≡⟨⟩
    rca (rca (I ∷ xs) (I ∷ (~ ys)) O) (I ∷ ys) O
  ≡⟨ cong (λ l → rca l (I ∷ ys) O) (rca-no-carry I xs I (~ ys)) ⟩
    rca ((I xor I) ∷ rca xs (~ ys) (I ∧ I)) (I ∷ ys) O
  ≡⟨ cong (λ l → rca (l ∷ rca xs (~ ys) (I ∧ I)) (I ∷ ys) O) (true-xorʳ I) ⟩
    rca (not I ∷ rca xs (~ ys) (I ∧ I)) (I ∷ ys) O
  ≡⟨ cong (λ l → rca (not I ∷ rca xs (~ ys) l) (I ∷ ys) O) (∧-identityʳ I) ⟩
    rca (not I ∷ rca xs (~ ys) I) (I ∷ ys) O
  ≡⟨ rca-no-carry (not I) (rca xs (~ ys) I) I ys ⟩
    (not I xor I) ∷ rca (rca xs (~ ys) I) ys (not I ∧ I)
  ≡⟨ cong (_∷ rca (rca xs (~ ys) I) ys (not I ∧ I)) (true-xorʳ (not I)) ⟩
    (not (not I)) ∷ rca (rca xs (~ ys) I) ys (not I ∧ I)
  ≡⟨ cong (_∷ rca (rca xs (~ ys) I) ys (not I ∧ I)) (not-involutive I) ⟩
    I ∷ rca (rca xs (~ ys) I) ys (not I ∧ I)
  ≡⟨ cong (λ l → I ∷ rca (rca xs (~ ys) I) ys l) (∧-identityʳ (not I)) ⟩
    I ∷ rca (rca xs (~ ys) I) ys O
  ≡⟨ cong (λ l → I ∷ rca l ys O) (rca-carry≡rca-incʳ xs (~ ys)) ⟩
    I ∷ rca (rca xs (inc (~ ys)) O) ys O
  ≡⟨ cong (λ l → I ∷ rca (rca xs l O) ys O) (negate≡inc-~ ys) ⟩
    I ∷ rca (rca xs (- ys) O) ys O
  ≡⟨ cong (I ∷_) (add-sub-involutive xs ys) ⟩
    I ∷ xs
  ∎ 
      