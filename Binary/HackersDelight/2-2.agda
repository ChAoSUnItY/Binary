module Binary.HackersDelight.2-2 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; cong-app; subst; trans; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Vec using (Vec; _∷_; []; map; foldl)
open import Data.Vec.Properties
open import Data.Nat using (ℕ; suc)
open import Data.Bool using (_∧_; _∨_; not; _xor_)
open import Data.Bool.Properties
open import Function.Base
open import Binary.Base
open import Binary.Properties
open import Binary.AddProperties

-- Equation (a), trivial as it's just definition of 2's complement.
nneg≡inc-~ : ∀ {n} (xs : Binary n) → - xs ≡ inc (~ xs)
nneg≡inc-~ xs = refl 

-- Equation (b)
nneg≡~-dec : ∀ {n} (xs : Binary n) → - xs ≡ ~ (dec xs)
nneg≡~-dec [] = refl
nneg≡~-dec {n} xs = begin
    - xs
  ≡⟨ sym (~-involutive (- xs)) ⟩
    (~ (~ (- xs)))
  ≡⟨ cong (~_) (~-nneg≡dec xs) ⟩
    ~ (dec xs)
  ∎
  where
    -- Also showed in equation (c)
    ~≡nneg-dec : ∀ {n} (xs : Binary n) → ~ xs ≡ dec (- xs)
    ~≡nneg-dec xs = begin
        ~ xs
      ≡⟨ sym (dec-inc-elim (~ xs)) ⟩
        dec (inc (~ xs))
      ≡⟨⟩
        dec (- xs)
      ∎

    -- Also showed in equation (e)
    ~-nneg≡dec : ∀ {n} (xs : Binary n) → ~ (- xs) ≡ dec xs
    ~-nneg≡dec xs = begin
        (~ (- xs))
      ≡⟨ ~≡nneg-dec (- xs) ⟩
        dec (- (- xs))
      ≡⟨ cong (dec) (nneg-involutive xs) ⟩
        dec xs
      ∎

-- Equation (c)
~≡nneg-dec : ∀ {n} (xs : Binary n) → ~ xs ≡ dec (- xs)
~≡nneg-dec xs = begin
    ~ xs
  ≡⟨ sym (dec-inc-elim (~ xs)) ⟩
    dec (inc (~ xs))
  ≡⟨⟩
    dec (- xs)
  ∎

-- Equation (d)
nneg-~≡inc : ∀ {n} (xs : Binary n) → - (~ xs) ≡ inc xs
nneg-~≡inc xs = begin
    - (~ xs)
  ≡⟨⟩
    inc (~ (~ xs))
  ≡⟨ cong (inc) (~-involutive xs) ⟩
    inc xs
  ∎

-- Equation (e)
~-nneg≡dec : ∀ {n} (xs : Binary n) → ~ (- xs) ≡ dec xs
~-nneg≡dec xs = begin
    (~ (- xs))
  ≡⟨ ~≡nneg-dec (- xs) ⟩
    dec (- (- xs))
  ≡⟨ cong (dec) (nneg-involutive xs) ⟩
    dec xs
  ∎

-- Equation (f)
+≡--~-dec : ∀ {n} (xs ys : Binary n) → xs + ys ≡ dec (xs - (~ ys))
+≡--~-dec xs ys = begin
    xs + ys
  ≡⟨ cong (xs +_) (sym (~-involutive ys)) ⟩
    xs + (~ (~ ys))
  ≡⟨ sym (dec-inc-elim (xs + (~ (~ ys)))) ⟩
    dec (inc (xs + (~ (~ ys))))
  ≡⟨ cong (dec) (sym (rca-inc-liftʳ xs (~ (~ ys)) O)) ⟩
    dec (xs - (~ ys))
  ∎

-- Equation (g)
HACKMEM-item-23-a : ∀ {n} (xs ys : Binary n) → xs + ys ≡ (xs ^ ys) + ((xs & ys) + (xs & ys))
HACKMEM-item-23-a [] [] = refl
HACKMEM-item-23-a (x ∷ xs) (y ∷ ys) rewrite xor-same (x ∧ y)
                                          | xor-identityʳ (x xor y)
                                          | xor-identityʳ (x xor y)
                                          | ∨-identityʳ (x ∧ y) = {!   !}

-- Equation (h)
HACKMEM-item-23-b : ∀ {n} (xs ys : Binary n) → xs + ys ≡ (xs ∥ ys) + (xs & ys)
HACKMEM-item-23-b [] [] = refl
HACKMEM-item-23-b (x ∷ xs) (y ∷ ys) with x | y
... | O | O = begin
    O ∷ xs + ys
  ≡⟨ cong (O ∷_) (HACKMEM-item-23-b xs ys) ⟩
    O ∷ (xs ∥ ys) + (xs & ys)
  ∎
... | I | O = begin
    I ∷ xs + ys
  ≡⟨ cong (I ∷_) (HACKMEM-item-23-b xs ys) ⟩
    I ∷ (xs ∥ ys) + (xs & ys)
  ∎
... | O | I = begin
    I ∷ xs + ys
  ≡⟨ cong (I ∷_) (HACKMEM-item-23-b xs ys) ⟩
    I ∷ (xs ∥ ys) + (xs & ys)
  ∎
... | I | I = begin
    O ∷ rca xs ys I
  ≡⟨ cong (O ∷_) (rca-carry-lift-inc xs ys) ⟩
    O ∷ inc (xs + ys)
  ≡⟨ cong (λ l → O ∷ inc l) (HACKMEM-item-23-b xs ys) ⟩
    O ∷ inc (rca (xs ∥ ys) (xs & ys) O)
  ≡⟨ cong (O ∷_) (sym (rca-carry-lift-inc (xs ∥ ys) (xs & ys))) ⟩
    O ∷ rca (xs ∥ ys) (xs & ys) I
  ∎

-- Equation (i)
+≡∥-+-∥-+-^ : ∀ {n} (xs ys : Binary n) → xs + ys ≡ ((xs ∥ ys) + (xs ∥ ys)) - (xs ^ ys)
+≡∥-+-∥-+-^ [] [] = refl
+≡∥-+-∥-+-^ (x ∷ xs) (y ∷ ys) with x | y
... | O | O = begin
    O ∷ xs + ys
  ≡⟨ cong (O ∷_) (+≡∥-+-∥-+-^ xs ys) ⟩
    O ∷ ((xs ∥ ys) + (xs ∥ ys)) - (xs ^ ys)
  ∎
... | I | O = begin
    I ∷ xs + ys
  ≡⟨ cong (I ∷_) (+≡∥-+-∥-+-^ xs ys) ⟩
    I ∷ ((xs ∥ ys) + (xs ∥ ys)) - (xs ^ ys)
  ≡⟨⟩
    I ∷ ((xs ∥ ys) + (xs ∥ ys)) + inc (~ (xs ^ ys))
  ≡⟨ cong (I ∷_) (sym (rca-inc-comm ((xs ∥ ys) + (xs ∥ ys)) (~ (xs ^ ys)) O)) ⟩
    I ∷ (inc ((xs ∥ ys) + (xs ∥ ys))) + (~ (xs ^ ys))
  ≡⟨ cong (λ l → I ∷ l + (~ (xs ^ ys))) (sym (rca-carry-lift-inc (xs ∥ ys) (xs ∥ ys))) ⟩
    I ∷ (rca (xs ∥ ys) (xs ∥ ys) I) + (~ (xs ^ ys))
  ∎
... | O | I = begin
    I ∷ xs + ys
  ≡⟨ cong (I ∷_) (+≡∥-+-∥-+-^ xs ys) ⟩
    I ∷ ((xs ∥ ys) + (xs ∥ ys)) - (xs ^ ys)
  ≡⟨⟩
    I ∷ ((xs ∥ ys) + (xs ∥ ys)) + inc (~ (xs ^ ys))
  ≡⟨ cong (I ∷_) (sym (rca-inc-comm ((xs ∥ ys) + (xs ∥ ys)) (~ (xs ^ ys)) O)) ⟩
    I ∷ (inc ((xs ∥ ys) + (xs ∥ ys))) + (~ (xs ^ ys))
  ≡⟨ cong (λ l → I ∷ l + (~ (xs ^ ys))) (sym (rca-carry-lift-inc (xs ∥ ys) (xs ∥ ys))) ⟩
    I ∷ (rca (xs ∥ ys) (xs ∥ ys) I) + (~ (xs ^ ys))
  ∎
... | I | I = begin
    O ∷ rca xs ys I
  ≡⟨ cong (O ∷_) (rca-carry-lift-inc xs ys) ⟩
    O ∷ inc (xs + ys)
  ≡⟨ cong (λ l → O ∷ inc l) (+≡∥-+-∥-+-^ xs ys) ⟩
    O ∷ inc (((xs ∥ ys) + (xs ∥ ys)) - (xs ^ ys))
  ≡⟨ cong (O ∷_) (sym (rca-inc-liftˡ ((xs ∥ ys) + (xs ∥ ys)) (- (xs ^ ys)) O)) ⟩
    O ∷ inc ((xs ∥ ys) + (xs ∥ ys)) - (xs ^ ys)
  ≡⟨ cong (λ l → O ∷ (l - (xs ^ ys))) (sym (rca-carry-lift-inc (xs ∥ ys) (xs ∥ ys))) ⟩
    O ∷ (rca (xs ∥ ys) (xs ∥ ys) I) - (xs ^ ys)
  ∎

-- Equation (j)
-≡+-~-+ : ∀ {n} (xs ys : Binary n) → xs - ys ≡ inc (xs + (~ ys))
-≡+-~-+ xs ys = begin
    xs - ys
  ≡⟨⟩
    xs + inc (~ ys)
  ≡⟨ rca-inc-liftʳ xs (~ ys) O ⟩
    inc (xs + (~ ys))
  ∎

-- Equation (k)
--
-- This theorem is extremely hard to be written in reasoning chain,
-- we'll leave this to readers :)
HACKMEM-item-23-a-dual : ∀ {n} (xs ys : Binary n) → xs - ys ≡ ((xs ^ ys) - ((~ xs) & ys)) - ((~ xs) & ys)
HACKMEM-item-23-a-dual [] [] = refl
HACKMEM-item-23-a-dual {suc n} (x ∷ xs) (y ∷ ys) with x | y
... | O | O rewrite HACKMEM-item-23-a-dual xs ys = refl
... | I | O rewrite HACKMEM-item-23-a-dual xs ys = refl
... | O | I rewrite rca-carry-transpose-incʳ (xs ^ ys) (~ ((~ xs) & ys)) = inc-inj (
  begin
    inc (I ∷ xs + (~ ys))
  ≡⟨⟩
    O ∷ inc (xs + (~ ys))
  ≡⟨ cong (O ∷_) (trans (sym (rca-inc-liftʳ xs (~ ys) O)) (HACKMEM-item-23-a-dual xs ys)) ⟩
    O ∷ (((xs ^ ys) - ((~ xs) & ys)) - ((~ xs) & ys))
  ≡⟨ cong (O ∷_) (rca-inc-liftʳ ((xs ^ ys) - ((~ xs) & ys)) (~ ((~ xs) & ys)) O) ⟩
    inc (I ∷ ((xs ^ ys) - ((~ xs) & ys)) + (~ ((~ xs) & ys)))
  ∎)
... | I | I rewrite rca-carry-transpose-incʳ xs (~ ys) 
                  | HACKMEM-item-23-a-dual xs ys = refl
