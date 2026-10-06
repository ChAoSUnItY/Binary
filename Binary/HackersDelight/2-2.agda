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
open import Binary.HackersDelight.2-1

-- Equation (a), trivial as it's just definition of 2's complement.
eq-a : ∀ {n} (xs : Binary n) → - xs ≡ inc (~ xs)
eq-a xs = refl

-- Equation (b)
eq-b : ∀ {n} (xs : Binary n) → - xs ≡ ~ (dec xs)
eq-b xs = begin
    - xs
  ≡⟨⟩
    inc (~ xs)
  ≡⟨ sym (~-dec≡inc-~ xs) ⟩
    ~ (dec xs)
  ∎

-- Equation (c)
eq-c : ∀ {n} (xs : Binary n) → ~ xs ≡ dec (- xs)
eq-c xs = begin
    ~ xs
  ≡⟨ sym (dec-inc-elim (~ xs)) ⟩
    dec (inc (~ xs))
  ≡⟨⟩
    dec (- xs)
  ∎

-- Equation (d)
eq-d : ∀ {n} (xs : Binary n) → - (~ xs) ≡ inc xs
eq-d xs = begin
    - (~ xs)
  ≡⟨⟩
    inc (~ (~ xs))
  ≡⟨ cong (inc) (~-involutive xs) ⟩
    inc xs
  ∎

-- Equation (e)
eq-e : ∀ {n} (xs : Binary n) → ~ (- xs) ≡ dec xs
eq-e xs = ~-nneg≡dec xs

-- Equation (f)
eq-f : ∀ {n} (xs ys : Binary n) → xs + ys ≡ dec (xs - (~ ys))
eq-f xs ys = begin
    xs + ys
  ≡⟨ cong (xs +_) (sym (~-involutive ys)) ⟩
    xs + (~ (~ ys))
  ≡⟨ sym (dec-inc-elim (xs + (~ (~ ys)))) ⟩
    dec (inc (xs + (~ (~ ys))))
  ≡⟨ cong (dec) (sym (rca-inc-liftʳ xs (~ (~ ys)) O)) ⟩
    dec (xs - (~ ys))
  ∎

-- Equation (g)
eq-g : ∀ {n} (xs ys : Binary n) → xs + ys ≡ (xs ^ ys) + ((xs & ys) + (xs & ys))
eq-g [] [] = refl
eq-g (x ∷ xs) (y ∷ ys) rewrite inc?-lift (x ∧ y ∨ O) xs ys
                             | eq-g xs ys with add-result x y
... | case-zero h1 h2 rewrite h1
                            | h2 
                            = refl
... | case-one x∧y _ x⊕y rewrite x∧y
                               | x⊕y 
                               = refl
... | case-carry h1 h2 rewrite h1
                             | h2
                             | rca-carry-lift-inc (xs & ys) (xs & ys)
                             | rca-inc-liftʳ (xs ^ ys) ((xs & ys) + (xs & ys)) O 
                             = refl

-- Equation (h)
eq-h : ∀ {n} (xs ys : Binary n) → xs + ys ≡ (xs ∥ ys) + (xs & ys)
eq-h [] [] = refl
eq-h (x ∷ xs) (y ∷ ys) rewrite inc?-lift (x ∧ y ∨ O) xs ys
                             | eq-h xs ys with add-result x y
... | case-zero h1 h2 rewrite h1
                            | h2 
                            = refl
... | case-one x∧y x∨y x⊕y rewrite x∧y
                                 | x∨y
                                 | x⊕y 
                                 = refl
... | case-carry h1 h2 rewrite h1
                             | h2
                             | sym (rca-carry-lift-inc (xs ∥ ys) (xs & ys)) 
                             = refl

-- Equation (i)
eq-i : ∀ {n} (xs ys : Binary n) → xs + ys ≡ ((xs ∥ ys) + (xs ∥ ys)) - (xs ^ ys)
eq-i [] [] = refl
eq-i (x ∷ xs) (y ∷ ys) rewrite inc?-lift (x ∧ y ∨ O) xs ys
                             | eq-i xs ys with add-result x y
... | case-zero h1 h2 rewrite h1
                            | h2 
                            = refl
... | case-one x∧y x∨y x⊕y rewrite x∧y
                                 | x∨y
                                 | x⊕y
                                 | sym (rca-inc-comm ((xs ∥ ys) + (xs ∥ ys)) (~ (xs ^ ys)) O)
                                 | sym (rca-carry-lift-inc (xs ∥ ys) (xs ∥ ys)) 
                                 = refl
... | case-carry h1 h2 rewrite h1
                             | h2
                             | sym (rca-carry-lift-inc ((xs ∥ ys) + (xs ∥ ys)) (- (xs ^ ys)))
                             | rca-carry-transpose-incˡ ((xs ∥ ys) + (xs ∥ ys)) (- (xs ^ ys))
                             | sym (rca-carry-lift-inc (xs ∥ ys) (xs ∥ ys)) 
                             = refl

-- Equation (j)
eq-j : ∀ {n} (xs ys : Binary n) → xs - ys ≡ inc (xs + (~ ys))
eq-j xs ys = begin
    xs - ys
  ≡⟨⟩
    xs + inc (~ ys)
  ≡⟨ rca-inc-liftʳ xs (~ ys) O ⟩
    inc (xs + (~ ys))
  ∎

-- Equation (k)
eq-k : ∀ {n} (xs ys : Binary n) → xs - ys ≡ ((xs ^ ys) - ((~ xs) & ys)) - ((~ xs) & ys)
eq-k xs ys = begin
    xs - ys
  ≡⟨ sym (~-involutive (xs - ys)) ⟩
    ~ (~ (xs - ys))
  ≡⟨ cong (~_) (~--≡~ˡ-+ xs ys) ⟩
    ~ ((~ xs) + ys)
  ≡⟨ cong (~_) (eq-g (~ xs) ys) ⟩
    ~ (((~ xs) ^ ys) + (((~ xs) & ys) + ((~ xs) & ys)))
  ≡⟨ ~-+≡~ˡ-- ((~ xs) ^ ys) (((~ xs) & ys) + ((~ xs) & ys)) ⟩
    (~ ((~ xs) ^ ys)) - (((~ xs) & ys) + ((~ xs) & ys))
  ≡⟨ cong (λ l → (~ l) - (((~ xs) & ys) + ((~ xs) & ys))) (sym (~-^≡~ˡ-^ xs ys)) ⟩
    (~ (~ (xs ^ ys))) - (((~ xs) & ys) + ((~ xs) & ys))
  ≡⟨ cong (λ l → l - (((~ xs) & ys) + ((~ xs) & ys))) (~-involutive (xs ^ ys)) ⟩
    (xs ^ ys) - (((~ xs) & ys) + ((~ xs) & ys))
  ≡⟨ cong ((xs ^ ys) +_) (nneg-distrib ((~ xs) & ys) ((~ xs) & ys)) ⟩
    (xs ^ ys) + ((- ((~ xs) & ys)) + (- ((~ xs) & ys)))
  ≡⟨ sym (+-assoc (xs ^ ys) (- ((~ xs) & ys)) (- ((~ xs) & ys))) ⟩
    ((xs ^ ys) - ((~ xs) & ys)) - ((~ xs) & ys)
  ∎

-- Eqaution (l)
eq-l : ∀ {n} (xs ys : Binary n) → xs - ys ≡ (xs & (~ ys)) - ((~ xs) & ys)
eq-l xs ys = begin
    xs - ys
  ≡⟨ sym (~-involutive (xs - ys)) ⟩
    ~ (~ (xs - ys))
  ≡⟨ cong (~_) (~--≡~ˡ-+ xs ys) ⟩
    ~ ((~ xs) + ys)
  ≡⟨ cong (~_) (eq-h (~ xs) ys) ⟩
    (~ (((~ xs) ∥ ys) + ((~ xs) & ys)))
  ≡⟨ ~-+≡~ˡ-- ((~ xs) ∥ ys) ((~ xs) & ys) ⟩
    ~ (~ xs ∥ ys) - (~ xs & ys)
  ≡⟨ cong (λ l → l - (~ xs & ys)) (~-∥-distrib (~ xs) ys) ⟩
    (~ (~ xs) & ~ ys) - (~ xs & ys)
  ≡⟨ cong (λ l → (l & ~ ys) - (~ xs & ys)) (~-involutive xs) ⟩
    (xs & ~ ys) - (~ xs & ys)
  ∎

-- Eqaution (m)
eq-m : ∀ {n} (xs ys : Binary n) → xs - ys ≡ ((xs & ~ ys) + (xs & ~ ys)) - (xs ^ ys)
eq-m xs ys = begin
    xs - ys
  ≡⟨ eq-j xs ys ⟩
    inc (xs + ~ ys)
  ≡⟨ cong inc (eq-g xs (~ ys)) ⟩
    inc ((xs ^ ~ ys) + ((xs & ~ ys) + (xs & ~ ys)))
  ≡⟨ cong (λ l → inc (l + ((xs & ~ ys) + (xs & ~ ys)))) (^-comm xs (~ ys)) ⟩
    inc ((~ ys ^ xs) + ((xs & ~ ys) + (xs & ~ ys)))
  ≡⟨ cong (λ l → inc (l + ((xs & ~ ys) + (xs & ~ ys)))) (sym (~-^≡~ˡ-^ ys xs)) ⟩
    inc (~ (ys ^ xs) + ((xs & ~ ys) + (xs & ~ ys)))
  ≡⟨ cong (λ l → inc (~ l + ((xs & ~ ys) + (xs & ~ ys)))) (^-comm ys xs) ⟩
    inc (~ (xs ^ ys) + ((xs & ~ ys) + (xs & ~ ys)))
  ≡⟨ cong inc (+-comm (~ (xs ^ ys)) ((xs & ~ ys) + (xs & ~ ys))) ⟩
    inc (((xs & ~ ys) + (xs & ~ ys)) + ~ (xs ^ ys))
  ≡⟨ sym (eq-j ((xs & ~ ys) + (xs & ~ ys)) (xs ^ ys)) ⟩
    ((xs & ~ ys) + (xs & ~ ys)) - (xs ^ ys)
  ∎

-- Eqaution (n)
eq-n : ∀ {n} (xs ys : Binary n) → xs ^ ys ≡ (xs ∥ ys) - (xs & ys)
eq-n [] [] = refl
eq-n (x ∷ xs) (y ∷ ys) rewrite eq-n xs ys with add-result x y
... | case-zero h1 h2 rewrite h1
                            | h2 
                            = refl
... | case-one x∧y x∨y x⊕y rewrite x∧y
                                 | x∨y
                                 | x⊕y
                                 = refl
... | case-carry h1 h2 rewrite h1
                             | h2
                             | rca-carry-transpose-incʳ (xs ∥ ys) (~ (xs & ys))
                             = refl

-- Eqaution (o)
eq-o : ∀ {n} (xs ys : Binary n) → xs & (~ ys) ≡ (xs ∥ ys) - ys
eq-o [] [] = refl
eq-o (x ∷ xs) (y ∷ ys) rewrite eq-o xs ys with x | y
... | O | O = refl
... | O | I rewrite sym (rca-carry-transpose-incʳ (xs ∥ ys) (~ ys)) = refl
... | I | O = refl
... | I | I rewrite sym (rca-carry-transpose-incʳ (xs ∥ ys) (~ ys)) = refl

-- Eqaution (p)
eq-p : ∀ {n} (xs ys : Binary n) → xs & (~ ys) ≡ xs - (xs & ys)
eq-p [] [] = refl
eq-p (x ∷ xs) (y ∷ ys) rewrite eq-p xs ys with x | y
... | O | O = refl
... | O | I = refl
... | I | O = refl
... | I | I rewrite rca-carry-transpose-incʳ (xs) (~ (xs & ys)) = refl

-- Eqaution (q)
eq-q : ∀ {n} (xs ys : Binary n) → ~ (xs - ys) ≡ dec (ys - xs)
eq-q {n} xs ys = begin
    ~ (xs - ys)
  ≡⟨ ~--≡~ˡ-+ xs ys ⟩
    ~ xs + ys
  ≡⟨ cong (λ l → l + ys) (eq-c xs) ⟩
    dec (- xs) + ys
  ≡⟨ cong (_+ ys) (sym (+-ones≡dec (- xs))) ⟩
    - xs + ones n + ys
  ≡⟨ +-assoc (- xs) (ones n) ys ⟩
    - xs + (ones n + ys)
  ≡⟨ cong (- xs +_) (+-comm (ones n) ys) ⟩
    - xs + (ys + ones n)
  ≡⟨ sym (+-assoc (- xs) ys (ones n)) ⟩
    - xs + ys + ones n
  ≡⟨ cong (_+ ones n) (+-comm (- xs) ys) ⟩
    ys - xs + ones n
  ≡⟨ +-ones≡dec (ys - xs) ⟩
    dec (ys - xs)
  ∎

-- Eqaution (r)
eq-r : ∀ {n} (xs ys : Binary n) → ~ (xs - ys) ≡ (~ xs) + ys
eq-r xs ys = ~--≡~ˡ-+ xs ys

-- Eqaution (s)
eq-s : ∀ {n} (xs ys : Binary n) → xs == ys ≡ dec ((xs & ys) - (xs ∥ ys))
eq-s xs ys = begin
    xs == ys
  ≡⟨ sym (~-^≡== xs ys) ⟩
    ~ (xs ^ ys)
  ≡⟨ eq-c (xs ^ ys) ⟩
    dec (- (xs ^ ys))
  ≡⟨ cong (λ l → dec (- l)) (eq-n xs ys) ⟩
    dec (- ((xs ∥ ys) - (xs & ys)))
  ≡⟨ cong dec (nneg-distrib (xs ∥ ys) (- (xs & ys))) ⟩
    dec (- (xs ∥ ys) + - (- (xs & ys)))
  ≡⟨ cong (λ l → dec (- (xs ∥ ys) + l)) (nneg-involutive (xs & ys)) ⟩
    dec (- (xs ∥ ys) + (xs & ys))
  ≡⟨ cong dec (+-comm (- (xs ∥ ys)) (xs & ys)) ⟩
    dec ((xs & ys) - (xs ∥ ys))
  ∎

-- Eqaution (t)
eq-t : ∀ {n} (xs ys : Binary n) → xs == ys ≡ (xs & ys) + ~ (xs ∥ ys)
eq-t xs ys = begin
    xs == ys
  ≡⟨ eq-s xs ys ⟩
    dec ((xs & ys) - (xs ∥ ys))
  ≡⟨ sym (eq-e ((xs & ys) - (xs ∥ ys))) ⟩
    ~ (- ((xs & ys) - (xs ∥ ys)))
  ≡⟨ cong (~_) (nneg-distrib (xs & ys) (- (xs ∥ ys))) ⟩
    ~ (- (xs & ys) + - (- (xs ∥ ys)))
  ≡⟨ cong (λ l → ~ (- (xs & ys) + l)) (nneg-involutive (xs ∥ ys)) ⟩
    ~ (- (xs & ys) + (xs ∥ ys))
  ≡⟨ ~-+≡~ˡ-- (- (xs & ys)) (xs ∥ ys) ⟩
    ~ (- (xs & ys)) - (xs ∥ ys)
  ≡⟨ cong (λ l → l - (xs ∥ ys)) (~-nneg≡dec (xs & ys)) ⟩
    dec (xs & ys) - (xs ∥ ys)
  ≡⟨ sym (rca-inc-comm (dec (xs & ys)) (~ (xs ∥ ys)) O) ⟩
    inc (dec (xs & ys)) + ~ (xs ∥ ys)
  ≡⟨ cong (λ l → l + ~ (xs ∥ ys)) (inc-dec-elim (xs & ys)) ⟩
    (xs & ys) + ~ (xs ∥ ys)
  ∎

-- Eqaution (u)
eq-u : ∀ {n} (xs ys : Binary n) → xs ∥ ys ≡ (xs & ~ ys) + ys
eq-u {n} xs ys = begin
    xs ∥ ys
  ≡⟨ sym (+-identityʳ (xs ∥ ys)) ⟩
    (xs ∥ ys) + zero n
  ≡⟨ cong ((xs ∥ ys) +_) (sym (+-elimˡ ys)) ⟩
    (xs ∥ ys) + (- ys + ys)
  ≡⟨ sym (+-assoc (xs ∥ ys) (- ys) ys) ⟩
    (xs ∥ ys) - ys + ys
  ≡⟨ cong (λ l → l + ys) (sym (eq-o xs ys)) ⟩
    (xs & ~ ys) + ys
  ∎

-- Eqaution (v)
eq-v : ∀ {n} (xs ys : Binary n) → xs & ys ≡ ((~ xs) ∥ ys) - ~ xs
eq-v {n} xs ys = begin
    xs & ys
  ≡⟨ &-comm xs ys ⟩
    ys & xs
  ≡⟨ cong (ys &_) (sym (~-involutive xs)) ⟩
    ys & ~ (~ xs)
  ≡⟨ eq-o ys (~ xs) ⟩
    (ys ∥ ~ xs) - ~ xs
  ≡⟨ cong (λ l → l - ~ xs) (∥-comm ys (~ xs)) ⟩
    (~ xs ∥ ys) - ~ xs
  ∎
