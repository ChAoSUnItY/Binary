module Bin.AddProperties where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; cong-app; subst; trans; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Vec using (Vec; _∷_; _∷ʳ_; []; _++_; replicate; map; zip; zipWith)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂; map₁)
open import Data.Nat using (ℕ; suc)
open import Data.Bool using (_∧_; _∨_; not; _xor_)
open import Data.Bool.Properties
open import Function
open import Tactic.Cong
open import Bin.Base
open import Bin.Properties

-- Basic RCA theorems
rca-no-carry : ∀ {n} (x y : Bit) (xs ys : Binary n) → rca (x ∷ xs) (y ∷ ys) O ≡ (x xor y) ∷ rca xs ys (x ∧ y)
rca-no-carry {n} x y xs ys = begin
    rca (x ∷ xs) (y ∷ ys) O
  ≡⟨⟩
    ((x xor y) xor O) ∷ rca xs ys (x ∧ y ∨ O ∧ (x xor y))
  ≡⟨ cong (_∷ rca xs ys (x ∧ y ∨ O ∧ (x xor y))) (xor-identityʳ (x xor y)) ⟩
    (x xor y) ∷ rca xs ys (x ∧ y ∨ O ∧ (x xor y))
  ≡⟨ cong! (∧-zeroˡ (x xor y)) ⟩
    (x xor y) ∷ rca xs ys (x ∧ y ∨ O)
  ≡⟨ cong! (∨-identityʳ (x ∧ y)) ⟩
    (x xor y) ∷ rca xs ys (x ∧ y)
  ≡⟨⟩
    (x xor y) ∷ rca xs ys (x ∧ y)
  ∎

-- Advanced RCA theorems
rca-comm : ∀ {n} (xs ys : Binary n) (c : Bit) → rca xs ys c ≡ rca ys xs c
rca-comm [] [] _ = refl
rca-comm (x ∷ xs) (y ∷ ys) c = begin
    rca (x ∷ xs) (y ∷ ys) c
  ≡⟨⟩
    ((x xor y) xor c) ∷ rca xs ys (x ∧ y ∨ c ∧ (x xor y))
  ≡⟨ cong (λ l → (l xor c) ∷ rca xs ys (x ∧ y ∨ c ∧ l)) (xor-comm x y) ⟩
    ((y xor x) xor c) ∷ rca xs ys (x ∧ y ∨ c ∧ (y xor x))
  ≡⟨ cong (λ l → ((y xor x) xor c) ∷ rca xs ys (l ∨ c ∧ (y xor x))) (∧-comm x y) ⟩
    ((y xor x) xor c) ∷ rca xs ys (y ∧ x ∨ c ∧ (y xor x))
  ≡⟨ cong (((y xor x) xor c) ∷_) (rca-comm xs ys (y ∧ x ∨ c ∧ (y xor x))) ⟩
    ((y xor x) xor c) ∷ rca ys xs (y ∧ x ∨ c ∧ (y xor x))
  ≡⟨ refl ⟩
    rca (y ∷ ys) (x ∷ xs) c
  ∎

rca-carry-transpose-incˡ : ∀ {n} (xs ys : Binary n) → rca xs ys I ≡ rca (inc xs) ys O
rca-carry-transpose-incˡ [] [] = refl
rca-carry-transpose-incˡ (O ∷ xs) (y ∷ ys) with y
... | O = refl
... | I = refl
rca-carry-transpose-incˡ (I ∷ xs) (O ∷ ys) = begin
    rca (I ∷ xs) (O ∷ ys) I
  ≡⟨⟩
    O ∷ rca xs ys I
  ≡⟨ cong (O ∷_) (rca-carry-transpose-incˡ xs ys) ⟩
    rca (inc (I ∷ xs)) (O ∷ ys) O
  ∎
rca-carry-transpose-incˡ (I ∷ xs) (I ∷ ys) = begin
    rca (I ∷ xs) (I ∷ ys) I
  ≡⟨⟩
    I ∷ rca xs ys I
  ≡⟨ cong (I ∷_) (rca-carry-transpose-incˡ xs ys) ⟩
    rca (inc (I ∷ xs)) (I ∷ ys) O
  ∎

rca-carry-transpose-incʳ : ∀ {n} (xs ys : Binary n) → rca xs ys I ≡ rca xs (inc ys) O
rca-carry-transpose-incʳ xs ys = begin
    rca xs ys I
  ≡⟨ rca-comm xs ys I ⟩
    rca ys xs I
  ≡⟨ rca-carry-transpose-incˡ ys xs ⟩
    rca (inc ys) xs O
  ≡⟨ rca-comm (inc ys) xs O ⟩
    rca xs (inc ys) O
  ∎

rca-carry-lift-inc : ∀ {n} (xs ys : Binary n) → rca xs ys I ≡ inc (rca xs ys O)
rca-carry-lift-inc [] [] = refl
rca-carry-lift-inc (x ∷ xs) (y ∷ ys) with x ∧ y in h1
... | I =
  begin
    ((x xor y) xor I) ∷ rca xs ys I
  ≡⟨ cong (λ l → (l xor I) ∷ rca xs ys I) (∧-true-implies-xor-false x y h1) ⟩
    (O xor I) ∷ rca xs ys I
  ≡⟨ cong (_∷ rca xs ys I) (xor-identityˡ I) ⟩
    I ∷ rca xs ys I
  ≡⟨⟩
    inc (O ∷ rca xs ys I)
  ≡⟨ cong (λ l → inc (l ∷ rca xs ys I)) (sym (∧-true-implies-xor-false x y h1)) ⟩
    inc ((x xor y) ∷ rca xs ys I)
  ≡⟨ cong (λ l → inc (l ∷ rca xs ys I)) (sym (xor-identityʳ (x xor y))) ⟩
    inc (((x xor y) xor O) ∷ rca xs ys I)
  ∎
... | O with x xor y in h2
...   | I = begin
    O ∷ rca xs ys I
  ≡⟨ cong (O ∷_) (rca-carry-lift-inc xs ys) ⟩
    O ∷ inc (rca xs ys O)
  ≡⟨⟩
    inc (I ∷ rca xs ys O)
  ∎
...   | O = refl

rca-inc-liftˡ : ∀ {n} (xs ys : Binary n) (c : Bit) → rca (inc xs) ys c ≡ inc (rca xs ys c)
rca-inc-liftˡ [] [] _ = refl
rca-inc-liftˡ xs ys O = begin
    rca (inc xs) ys O
  ≡⟨ sym (rca-carry-transpose-incˡ xs ys) ⟩
    rca xs ys I
  ≡⟨ rca-carry-lift-inc xs ys ⟩
    inc (rca xs ys O)
  ∎
rca-inc-liftˡ (x ∷ xs) (y ∷ ys) I with x | y
... | O | O = begin
    rca (inc (O ∷ xs)) (O ∷ ys) I
  ≡⟨⟩
    rca (I ∷ xs) (O ∷ ys) I
  ≡⟨⟩
    O ∷ rca xs ys I
  ≡⟨ cong (O ∷_) (rca-carry-lift-inc xs ys) ⟩
    O ∷ inc (rca xs ys O)
  ≡⟨⟩
    inc (I ∷ rca xs ys O)
  ∎
... | I | O = begin
    rca (inc (I ∷ xs)) (O ∷ ys) I
  ≡⟨⟩
    I ∷ rca (inc xs) ys O
  ≡⟨ cong (I ∷_) (sym (rca-carry-transpose-incˡ xs ys)) ⟩
    I ∷ rca xs ys I
  ≡⟨⟩
    inc (O ∷ rca xs ys I)
  ∎
... | O | I = refl
... | I | I = begin
    rca (inc (I ∷ xs)) (I ∷ ys) I
  ≡⟨⟩
    O ∷ rca (inc xs) ys I
  ≡⟨ cong (O ∷_) (rca-inc-liftˡ xs ys I) ⟩
    O ∷ inc (rca xs ys I)
  ≡⟨⟩
    inc (I ∷ rca xs ys I)
  ∎

rca-inc-liftʳ : ∀ {n} (xs ys : Binary n) (c : Bit) → rca xs (inc ys) c ≡ inc (rca xs ys c)
rca-inc-liftʳ xs ys c = begin
    rca xs (inc ys) c
  ≡⟨ rca-comm xs (inc ys) c ⟩
    rca (inc ys) xs c
  ≡⟨ rca-inc-liftˡ ys xs c ⟩
    inc (rca ys xs c)
  ≡⟨ cong (inc) (rca-comm ys xs c) ⟩
    inc (rca xs ys c)
  ∎

rca-inc-comm : ∀ {n} (xs ys : Binary n) (c : Bit) → rca (inc xs) ys c ≡ rca xs (inc ys) c
rca-inc-comm xs ys c = begin
    rca (inc xs) ys c
  ≡⟨ rca-inc-liftˡ xs ys c ⟩
    inc (rca xs ys c)
  ≡⟨ sym (rca-inc-liftʳ xs ys c) ⟩
    rca xs (inc ys) c
  ∎

rca-carry-commˡ : ∀ {n} (xs ys zs : Binary n) (c c' : Bit) → rca (rca xs ys c) zs c' ≡ rca (rca xs ys c') zs c
rca-carry-commˡ [] [] [] _ _ = refl
rca-carry-commˡ xs ys zs c c' with c | c'
... | O | O = refl
... | I | O = begin
    rca (rca xs ys I) zs O
  ≡⟨ cong (λ l → rca l zs O) (rca-carry-lift-inc xs ys) ⟩
    rca (inc (rca xs ys O)) zs O
  ≡⟨ sym (rca-carry-transpose-incˡ (rca xs ys O) zs) ⟩
    rca (rca xs ys O) zs I
  ∎
... | O | I = begin
    rca (rca xs ys O) zs I
  ≡⟨ rca-carry-transpose-incˡ (rca xs ys O) zs ⟩
    rca (inc (rca xs ys O)) zs O
  ≡⟨ cong (λ l → rca l zs O) (sym (rca-carry-lift-inc xs ys)) ⟩
    rca (rca xs ys I) zs O
  ∎
... | I | I = refl

rca-carry-commʳ : ∀ {n} (xs ys zs : Binary n) (c c' : Bit) → rca xs (rca ys zs c) c' ≡ rca xs (rca ys zs c') c
rca-carry-commʳ xs ys zs c c' = begin
    rca xs (rca ys zs c) c'
  ≡⟨ rca-comm xs (rca ys zs c) c' ⟩
    rca (rca ys zs c) xs c'
  ≡⟨ rca-carry-commˡ ys zs xs c c' ⟩
    rca (rca ys zs c') xs c
  ≡⟨ rca-comm (rca ys zs c') xs c ⟩
    rca xs (rca ys zs c') c
  ∎

rca-assoc-no-carry : ∀ {n} (xs ys zs : Binary n) → rca (rca xs ys O) zs O ≡ rca xs (rca ys zs O) O
rca-assoc-no-carry [] [] [] = refl
rca-assoc-no-carry (x ∷ xs) (y ∷ ys) (z ∷ zs) with x | y | z
... | O | O | O = begin
    O ∷ rca (rca xs ys O) zs O
  ≡⟨ cong (O ∷_) (rca-assoc-no-carry xs ys zs) ⟩
    O ∷ rca xs (rca ys zs O) O
  ∎
... | I | O | O = begin
    I ∷ rca (rca xs ys O) zs O
  ≡⟨ cong (I ∷_) (rca-assoc-no-carry xs ys zs) ⟩
    I ∷ rca xs (rca ys zs O) O
  ∎
... | O | I | O = begin
    I ∷ rca (rca xs ys O) zs O
  ≡⟨ cong (I ∷_) (rca-assoc-no-carry xs ys zs) ⟩
    I ∷ rca xs (rca ys zs O) O
  ∎
... | I | I | O = begin
    O ∷ rca (rca xs ys I) zs O
  ≡⟨ cong (O ∷_) (rca-carry-commˡ xs ys zs I O) ⟩
    O ∷ rca (rca xs ys O) zs I
  ≡⟨ cong (O ∷_) (rca-carry-lift-inc (rca xs ys O) zs) ⟩
    O ∷ inc (rca (rca xs ys O) zs O)
  ≡⟨ cong (λ l → O ∷ inc l) (rca-assoc-no-carry xs ys zs) ⟩
    O ∷ inc (rca xs (rca ys zs O) O)
  ≡⟨ cong (O ∷_) (sym (rca-carry-lift-inc xs (rca ys zs O))) ⟩
    O ∷ rca xs (rca ys zs O) I
  ∎
... | O | O | I = begin
    I ∷ rca (rca xs ys O) zs O
  ≡⟨ cong (I ∷_) (rca-assoc-no-carry xs ys zs) ⟩
    I ∷ rca xs (rca ys zs O) O
  ∎
... | I | O | I = begin
    O ∷ rca (rca xs ys O) zs I
  ≡⟨ cong (O ∷_) (rca-carry-lift-inc (rca xs ys O) zs) ⟩
    O ∷ inc (rca (rca xs ys O) zs O)
  ≡⟨ cong (λ l → O ∷ inc l) (rca-assoc-no-carry xs ys zs) ⟩
    O ∷ inc (rca xs (rca ys zs O) O)
  ≡⟨ cong (O ∷_) (sym (rca-carry-lift-inc xs (rca ys zs O))) ⟩
    O ∷ rca xs (rca ys zs O) I
  ∎
... | O | I | I = begin
    O ∷ rca (rca xs ys O) zs I
  ≡⟨ cong (O ∷_) (rca-carry-lift-inc (rca xs ys O) zs) ⟩
    O ∷ inc (rca (rca xs ys O) zs O)
  ≡⟨ cong (λ l → O ∷ inc l) (rca-assoc-no-carry xs ys zs) ⟩
    O ∷ inc (rca xs (rca ys zs O) O)
  ≡⟨ cong (O ∷_) (sym (rca-inc-liftʳ xs (rca ys zs O) O)) ⟩
    O ∷ rca xs (inc (rca ys zs O)) O
  ≡⟨ cong (λ l → O ∷ rca xs l O) (sym (rca-carry-lift-inc ys zs)) ⟩
    O ∷ rca xs (rca ys zs I) O
  ∎
... | I | I | I = begin
    I ∷ rca (rca xs ys I) zs O
  ≡⟨ cong (I ∷_) (rca-carry-commˡ xs ys zs I O) ⟩
    I ∷ rca (rca xs ys O) zs I
  ≡⟨ cong (I ∷_) (rca-carry-lift-inc (rca xs ys O) zs) ⟩
    I ∷ inc (rca (rca xs ys O) zs O)
  ≡⟨ cong (λ l → I ∷ inc l) (rca-assoc-no-carry xs ys zs) ⟩
    I ∷ inc (rca xs (rca ys zs O) O)
  ≡⟨ cong (I ∷_) (sym (rca-inc-liftʳ xs (rca ys zs O) O)) ⟩
    I ∷ rca xs (inc (rca ys zs O)) O
  ≡⟨ cong (λ l → I ∷ rca xs l O) (sym (rca-carry-lift-inc ys zs)) ⟩
    I ∷ rca xs (rca ys zs I) O
  ∎

rca-assoc : ∀ {n} (xs ys zs : Binary n) (c c' : Bit) → rca (rca xs ys c) zs c' ≡ rca xs (rca ys zs c) c'
rca-assoc xs ys zs O O = rca-assoc-no-carry xs ys zs
rca-assoc xs ys zs I O = begin
    rca (rca xs ys I) zs O
  ≡⟨ cong (λ l → rca l zs O) (rca-carry-lift-inc xs ys) ⟩
    rca (inc (rca xs ys O)) zs O
  ≡⟨ rca-inc-liftˡ (rca xs ys O) zs O ⟩
    inc (rca (rca xs ys O) zs O)
  ≡⟨ cong (inc) (rca-assoc-no-carry xs ys zs) ⟩
    inc (rca xs (rca ys zs O) O)
  ≡⟨ sym (rca-inc-liftʳ xs (rca ys zs O) O) ⟩
    rca xs (inc (rca ys zs O)) O
  ≡⟨ cong (λ l → rca xs l O) (sym (rca-carry-lift-inc ys zs)) ⟩
    rca xs (rca ys zs I) O
  ∎
rca-assoc xs ys zs O I = begin
    rca (rca xs ys O) zs I
  ≡⟨ rca-carry-lift-inc (rca xs ys O) zs ⟩
    inc (rca (rca xs ys O) zs O)
  ≡⟨ cong (inc) (rca-assoc-no-carry xs ys zs) ⟩
    inc (rca xs (rca ys zs O) O)
  ≡⟨ sym (rca-carry-lift-inc xs (rca ys zs O)) ⟩
    rca xs (rca ys zs O) I
  ∎
rca-assoc xs ys zs I I = begin
    rca (rca xs ys I) zs I
  ≡⟨ rca-carry-lift-inc (rca xs ys I) zs ⟩
    inc (rca (rca xs ys I) zs O)
  ≡⟨ cong (λ l → inc (rca l zs O)) (rca-carry-lift-inc xs ys) ⟩
    inc (rca (inc (rca xs ys O)) zs O)
  ≡⟨ cong (inc) (rca-inc-liftˡ (rca xs ys O) zs O) ⟩
    inc (inc (rca (rca xs ys O) zs O))
  ≡⟨ cong (λ l → inc (inc l)) (rca-assoc-no-carry xs ys zs) ⟩
    inc (inc (rca xs (rca ys zs O) O))
  ≡⟨ cong (inc) (sym (rca-inc-liftʳ xs (rca ys zs O) O)) ⟩
    inc (rca xs (inc (rca ys zs O)) O)
  ≡⟨ cong (λ l → inc (rca xs l O)) (sym (rca-carry-lift-inc ys zs)) ⟩
    inc (rca xs (rca ys zs I) O)
  ≡⟨ sym (rca-carry-lift-inc xs (rca ys zs I)) ⟩
    rca xs (rca ys zs I) I
  ∎

-- Actual addition theorems to be used with
+-comm : ∀ {n} (xs ys : Binary n) → xs + ys ≡ ys + xs
+-comm xs ys = rca-comm xs ys O

+-identityˡ : ∀ {n} (xs : Binary n) → zero n + xs ≡ xs
+-identityˡ {_}     [] = refl
+-identityˡ {suc n} (x ∷ xs) = begin
    zero (suc n) + (x ∷ xs)
  ≡⟨⟩
    ((O xor x) xor O) ∷ (zero n + xs)
  ≡⟨ cong (_∷ (zero n + xs)) (xor-identityʳ x) ⟩
    x ∷ (zero n + xs)
  ≡⟨ cong (x ∷_) (+-identityˡ xs) ⟩
    x ∷ xs
  ∎

+-identityʳ : ∀ {n} (xs : Binary n) → xs + zero n ≡ xs
+-identityʳ {n} xs = begin
    xs + zero n
  ≡⟨ +-comm xs (zero n) ⟩
    zero n + xs
  ≡⟨ +-identityˡ xs ⟩
    xs
  ∎

+-elimˡ : ∀ {n} (xs : Binary n) → (- xs) + xs ≡ zero n
+-elimˡ {_}     [] = refl
+-elimˡ {suc n} (x ∷ xs) with x
... | O = begin
    (- (O ∷ xs)) + (O ∷ xs)
  ≡⟨⟩
    O ∷ ((- xs) + xs)
  ≡⟨ cong (O ∷_) (+-elimˡ xs) ⟩
    zero (suc n)
  ∎
... | I = begin
    (- (I ∷ xs)) + (I ∷ xs)
  ≡⟨⟩
    O ∷ rca (map not xs) xs I
  ≡⟨ cong (O ∷_) (rca-carry-transpose-incˡ (map not xs) xs) ⟩
    O ∷ ((- xs) + xs)
  ≡⟨ cong (O ∷_) (+-elimˡ xs) ⟩
    zero (suc n)
  ∎

+-elimʳ : ∀ {n} (xs : Binary n) → xs + (- xs) ≡ zero n
+-elimʳ {n} xs = begin
    xs + (- xs)
  ≡⟨ +-comm xs (- xs) ⟩
    (- xs) + xs
  ≡⟨ +-elimˡ xs ⟩
    zero n
  ∎

+-assoc : ∀ {n} (xs ys zs : Binary n) → (xs + ys) + zs ≡ xs + (ys + zs)
+-assoc = rca-assoc-no-carry

-- Additional theorems for rca
~-+-ones : ∀ {n} (xs : Binary n) → xs + (~ xs) ≡ ones n
~-+-ones [] = refl
~-+-ones (x ∷ xs) with x
... | O rewrite ~-+-ones xs = refl
... | I rewrite ~-+-ones xs = refl
