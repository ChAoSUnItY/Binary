module Binary.HackersDelight.2-1 where

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

-- Prerequisite theorems
not-∧-distrib : ∀ (x y : Bit) → not (x ∧ y) ≡ (not x) ∨ (not y)
not-∧-distrib x y with x
... | O = refl
... | I = refl

not-∨-distrib : ∀ (x y : Bit) → not (x ∨ y) ≡ (not x) ∧ (not y)
not-∨-distrib x y with x
... | O = refl
... | I = refl

-- Actual extended laws
~-&-distrib : ∀ {n} (xs ys : Binary n) → ~ (xs & ys) ≡ (~ xs) ∥ (~ ys)
~-&-distrib [] [] = refl
~-&-distrib (x ∷ xs) (y ∷ ys) = begin
    (~ ((x ∷ xs) & (y ∷ ys)))
  ≡⟨⟩
    not (x ∧ y) ∷ ~ (xs & ys)
  ≡⟨ cong₂ (_∷_) (not-∧-distrib x y) (~-&-distrib xs ys) ⟩
    ((~ (x ∷ xs)) ∥ (~ (y ∷ ys)))
  ∎

~-∥-distrib : ∀ {n} (xs ys : Binary n) → ~ (xs ∥ ys) ≡ (~ xs) & (~ ys)
~-∥-distrib [] [] = refl
~-∥-distrib (x ∷ xs) (y ∷ ys) = begin
    (~ ((x ∷ xs) ∥ (y ∷ ys)))
  ≡⟨⟩
    not (x ∨ y) ∷ ~ (xs ∥ ys)
  ≡⟨ cong₂ (_∷_) (not-∨-distrib x y) (~-∥-distrib xs ys) ⟩
    ((~ (x ∷ xs)) & (~ (y ∷ ys)))
  ∎

~-inc≡dec-~ : ∀ {n} (xs : Binary n) → ~ (inc xs) ≡ dec (~ xs)
~-inc≡dec-~ [] = refl
~-inc≡dec-~ (x ∷ xs) with x
... | O = refl
... | I = begin
    ~ inc (I ∷ xs)
  ≡⟨⟩
    I ∷ ~ (inc xs)
  ≡⟨ cong (I ∷_) (~-inc≡dec-~ xs) ⟩
    I ∷ dec (~ xs)
  ≡⟨⟩
    dec (~ (I ∷ xs))
  ∎

~-dec≡inc-~ : ∀ {n} (xs : Binary n) → ~ (dec xs) ≡ inc (~ xs)
~-dec≡inc-~ [] = refl
~-dec≡inc-~ (x ∷ xs) with x
... | O = begin
    ~ (dec (O ∷ xs))
  ≡⟨⟩
    O ∷ ~ (dec xs)
  ≡⟨ cong (O ∷_) (~-dec≡inc-~ xs) ⟩
    O ∷ inc (~ xs)
  ≡⟨⟩
    inc (~ (O ∷ xs))
  ∎
... | I = refl

~-^≡~ˡ-^ : ∀ {n} (xs ys : Binary n) → ~ (xs ^ ys) ≡ (~ xs) ^ ys
~-^≡~ˡ-^ [] [] = refl
~-^≡~ˡ-^ (x ∷ xs) (y ∷ ys) with x
... | O = begin
    (not y) ∷ ~ (xs ^ ys)
  ≡⟨ cong ((not y) ∷_) (~-^≡~ˡ-^ xs ys) ⟩
    (not y) ∷ (~ xs) ^ ys
  ∎
... | I = begin
    not (not y) ∷ ~ (xs ^ ys)
  ≡⟨ cong₂ (_∷_) (not-involutive y) (~-^≡~ˡ-^ xs ys) ⟩
    y ∷  (~ xs) ^ ys
  ∎

~-^≡== : ∀ {n} (xs ys : Binary n) → ~ (xs ^ ys) ≡ xs == ys
~-^≡== [] [] = refl
~-^≡== (x ∷ xs) (y ∷ ys) with x
... | O = begin
    (not y) ∷ ~ (xs ^ ys)
  ≡⟨ cong ((not y) ∷_) (~-^≡== xs ys) ⟩
    (not y) ∷ xs == ys
  ∎
... | I = begin
    not (not y) ∷ ~ (xs ^ ys)
  ≡⟨ cong₂ (_∷_) (not-involutive y) (~-^≡== xs ys) ⟩
    y ∷ xs == ys
  ∎

~-==≡~ˡ-== : ∀ {n} (xs ys : Binary n) → ~ (xs == ys) ≡ (~ xs) == ys
~-==≡~ˡ-== [] [] = refl
~-==≡~ˡ-== (x ∷ xs) (y ∷ ys) with x
... | O = begin
    not (not y) ∷ ~ (xs == ys)
  ≡⟨ cong₂ (_∷_) (not-involutive y) (~-==≡~ˡ-== xs ys) ⟩
    y ∷ (~ xs) == ys
  ∎
... | I = begin
    (not y) ∷ ~ (xs == ys)
  ≡⟨ cong ((not y) ∷_) (~-==≡~ˡ-== xs ys) ⟩
    (not y) ∷ (~ xs) == ys
  ∎

~-==≡^ : ∀ {n} (xs ys : Binary n) → ~ (xs == ys) ≡ xs ^ ys
~-==≡^ xs ys = begin
    ~ (xs == ys)
  ≡⟨ cong (~_) (sym (~-^≡== xs ys)) ⟩
    ~ (~ (xs ^ ys))
  ≡⟨ ~-involutive (xs ^ ys) ⟩
    xs ^ ys
  ∎

~-+≡~ˡ-- : ∀ {n} (xs ys : Binary n) → ~ (xs + ys) ≡ (~ xs) - ys
~-+≡~ˡ-- [] [] = refl
~-+≡~ˡ-- (x ∷ xs) (y ∷ ys) with x | y
... | O | O = begin
    I ∷ ~ (xs + ys)
  ≡⟨ cong (I ∷_) (~-+≡~ˡ-- xs ys) ⟩
    I ∷ ((~ xs) - ys)
  ≡⟨⟩
    (~ (O ∷ xs)) - (O ∷ ys)
  ∎
... | I | O = begin
    O ∷ ~ (xs + ys)
  ≡⟨ cong (O ∷_) (~-+≡~ˡ-- xs ys) ⟩
    (~ (I ∷ xs)) - (O ∷ ys)
  ∎
... | O | I = begin
    O ∷ ~ (xs + ys)
  ≡⟨ cong (O ∷_) (~-+≡~ˡ-- xs ys) ⟩
    O ∷ (~ xs) - ys
  ≡⟨⟩
    O ∷ (~ xs) + inc (~ ys)
  ≡⟨ cong (O ∷_) (sym (rca-carry-transpose-incʳ (~ xs) (~ ys))) ⟩
    O ∷ rca (~ xs) (~ ys) I
  ≡⟨⟩
    (~ (O ∷ xs)) - (I ∷ ys)
  ∎
... | I | I = begin
    I ∷ ~ (rca xs ys I)
  ≡⟨ cong (λ l → I ∷ ~ l) (rca-carry-lift-inc xs ys) ⟩
    I ∷ ~ (inc (xs + ys))
  ≡⟨ cong (I ∷_) (~-inc≡dec-~ (xs + ys)) ⟩
    I ∷ dec (~ (xs + ys))
  ≡⟨ cong (λ l → I ∷ dec l) (~-+≡~ˡ-- xs ys) ⟩
    I ∷ dec ((~ xs) + inc (~ ys))
  ≡⟨ cong (λ l → I ∷ dec l) (rca-inc-liftʳ (~ xs) (~ ys) O) ⟩
    I ∷ dec (inc ((~ xs) + (~ ys)))
  ≡⟨ cong (I ∷_) (dec-inc-elim ((~ xs) + (~ ys))) ⟩
    I ∷ (~ xs) + (~ ys)
  ≡⟨⟩
    ((~ (I ∷ xs)) - (I ∷ ys))
  ∎

~--≡~ˡ-+ : ∀ {n} (xs ys : Binary n) → ~ (xs - ys) ≡ (~ xs) + ys
~--≡~ˡ-+ xs ys = begin
    ~ (xs - ys)
  ≡⟨ ~-+≡~ˡ-- xs (- ys) ⟩
    (~ xs) - (- ys)
  ≡⟨⟩
    (~ xs) + (- (- ys))
  ≡⟨ cong ((~ xs) +_) (nneg-involutive ys) ⟩
    (~ xs) + ys
  ∎