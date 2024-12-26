module Bin.TestProperties where

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
open import Bin.Properties

rca-lift-carry : ∀ {n} (xs ys : Binary n) → rca xs ys I ≡ inc (rca xs ys O)
rca-lift-carry [] [] = refl
rca-lift-carry (O ∷ xs) (O ∷ ys) = refl
rca-lift-carry (O ∷ xs) (I ∷ ys) = begin
    rca (O ∷ xs) (I ∷ ys) I
  ≡⟨⟩
    O ∷ rca xs ys I
  ≡⟨ cong (O ∷_) (rca-lift-carry xs ys) ⟩
    O ∷ inc (rca xs ys O)
  ≡⟨⟩
    inc (rca (O ∷ xs) (I ∷ ys) O)
  ∎
rca-lift-carry (I ∷ xs) (O ∷ ys) = begin
    rca (I ∷ xs) (O ∷ ys) I
  ≡⟨⟩
    O ∷ rca xs ys I
  ≡⟨ cong (O ∷_) (rca-lift-carry xs ys) ⟩
    O ∷ inc (rca xs ys O)
  ≡⟨⟩
    inc (rca (I ∷ xs) (O ∷ ys) O)
  ∎
rca-lift-carry (I ∷ xs) (I ∷ ys) = refl

rca-lift-incˡ : ∀ {n} {carry : Bit} (xs ys : Binary n) → rca (inc xs) ys carry ≡ inc (rca xs ys carry)
rca-lift-incˡ [] [] = refl
rca-lift-incˡ {suc n} {O} (O ∷ xs) (O ∷ ys) = refl
rca-lift-incˡ {suc n} {O} (O ∷ xs) (I ∷ ys) rewrite rca-lift-carry xs ys = refl
rca-lift-incˡ {suc n} {O} (I ∷ xs) (O ∷ ys) rewrite rca-lift-incˡ {n} {O} xs ys = refl
rca-lift-incˡ {suc n} {O} (I ∷ xs) (I ∷ ys) rewrite rca-lift-incˡ {n} {O} xs ys | sym (rca-lift-carry xs ys) = refl
rca-lift-incˡ {suc n} {I} (O ∷ xs) (O ∷ ys) rewrite rca-lift-carry xs ys = refl
rca-lift-incˡ {suc n} {I} (O ∷ xs) (I ∷ ys) = refl
rca-lift-incˡ {suc n} {I} (I ∷ xs) (O ∷ ys) rewrite rca-lift-incˡ {n} {O} xs ys | sym (rca-lift-carry xs ys) = refl
rca-lift-incˡ {suc n} {I} (I ∷ xs) (I ∷ ys) rewrite rca-lift-incˡ {n} {I} xs ys = refl

rca-lift-incʳ : ∀ {n} {carry : Bit} (xs ys : Binary n) → rca xs (inc ys) carry ≡ inc (rca xs ys carry)
rca-lift-incʳ [] [] = refl
rca-lift-incʳ {suc n} {O} (O ∷ xs) (O ∷ ys) = refl
rca-lift-incʳ {suc n} {O} (O ∷ xs) (I ∷ ys) rewrite rca-lift-incʳ {n} {O} xs ys = refl
rca-lift-incʳ {suc n} {O} (I ∷ xs) (O ∷ ys) rewrite rca-lift-carry xs ys = refl
rca-lift-incʳ {suc n} {O} (I ∷ xs) (I ∷ ys) rewrite rca-lift-incʳ {n} {O} xs ys | sym (rca-lift-carry xs ys) = refl
rca-lift-incʳ {suc n} {I} (O ∷ xs) (O ∷ ys) rewrite sym (rca-lift-carry xs ys) = refl
rca-lift-incʳ {suc n} {I} (O ∷ xs) (I ∷ ys) rewrite rca-lift-incʳ {n} {O} xs ys | sym (rca-lift-carry xs ys) = refl
rca-lift-incʳ {suc n} {I} (I ∷ xs) (O ∷ ys) = refl
rca-lift-incʳ {suc n} {I} (I ∷ xs) (I ∷ ys) rewrite rca-lift-incʳ {n} {I} xs ys = refl

add-assocˡ : ∀ {n} (xs ys zs : Binary n) → (xs + ys) + zs ≡ xs + (ys + zs)
add-assocˡ [] [] [] = refl
add-assocˡ (O ∷ xs) (O ∷ ys) (O ∷ zs) = begin
    (((O ∷ xs) + (O ∷ ys)) + (O ∷ zs))
  ≡⟨⟩
    O ∷ rca (rca xs ys O) zs O
  ≡⟨ cong (O ∷_) (add-assocˡ xs ys zs) ⟩
    O ∷ rca xs (rca ys zs O) O
  ≡⟨ refl ⟩
    ((O ∷ xs) + ((O ∷ ys) + (O ∷ zs)))
  ∎
add-assocˡ (O ∷ xs) (O ∷ ys) (I ∷ zs) = begin
    (((O ∷ xs) + (O ∷ ys)) + (I ∷ zs))
  ≡⟨⟩
    I ∷ rca (rca xs ys O) zs O
  ≡⟨ cong (I ∷_) (add-assocˡ xs ys zs) ⟩
    I ∷ rca xs (rca ys zs O) O
  ≡⟨⟩
    ((O ∷ xs) + ((O ∷ ys) + (I ∷ zs)))
  ∎
add-assocˡ (O ∷ xs) (I ∷ ys) (O ∷ zs) = begin
    (((O ∷ xs) + (I ∷ ys)) + (O ∷ zs))
  ≡⟨⟩
    I ∷ rca (rca xs ys O) zs O
  ≡⟨ cong (I ∷_) (add-assocˡ xs ys zs) ⟩
    I ∷ rca xs (rca ys zs O) O
  ≡⟨⟩
    ((O ∷ xs) + ((I ∷ ys) + (O ∷ zs)))
  ∎
add-assocˡ (O ∷ xs) (I ∷ ys) (I ∷ zs) = begin
    (((O ∷ xs) + (I ∷ ys)) + (I ∷ zs))
  ≡⟨⟩
    O ∷ rca (rca xs ys O) zs I
  ≡⟨ cong (O ∷_) (rca-lift-carry (rca xs ys O) zs) ⟩
    O ∷ inc (rca (rca xs ys O) zs O)
  ≡⟨ cong (λ l → O ∷ inc l) (add-assocˡ xs ys zs) ⟩
    O ∷ inc (rca xs (rca ys zs O) O)
  ≡⟨ cong (O ∷_) (sym (rca-lift-incʳ xs (rca ys zs O))) ⟩
    O ∷ rca xs (inc (rca ys zs O)) O
  ≡⟨ cong (λ l → O ∷ rca xs l O) (sym (rca-lift-carry ys zs)) ⟩
    O ∷ rca xs (rca ys zs I) O
  ≡⟨⟩
    ((O ∷ xs) + ((I ∷ ys) + (I ∷ zs)))
  ∎
add-assocˡ (I ∷ xs) (O ∷ ys) (O ∷ zs) = begin
    (((I ∷ xs) + (O ∷ ys)) + (O ∷ zs))
  ≡⟨⟩
    I ∷ rca (rca xs ys O) zs O
  ≡⟨ cong (I ∷_) (add-assocˡ xs ys zs) ⟩
    I ∷ rca xs (rca ys zs O) O
  ≡⟨⟩
    ((I ∷ xs) + ((O ∷ ys) + (O ∷ zs)))
  ∎
add-assocˡ (I ∷ xs) (O ∷ ys) (I ∷ zs) = begin
    (((I ∷ xs) + (O ∷ ys)) + (I ∷ zs))
  ≡⟨⟩
    O ∷ rca (rca xs ys O) zs I
  ≡⟨ cong (O ∷_) (rca-lift-carry (rca xs ys O) zs) ⟩
    O ∷ inc (rca (rca xs ys O) zs O)
  ≡⟨ cong (λ l → O ∷ inc l) (add-assocˡ xs ys zs) ⟩
    O ∷ inc (rca xs (rca ys zs O) O)
  ≡⟨ cong (O ∷_) (sym (rca-lift-carry xs (rca ys zs O))) ⟩
    O ∷ rca xs (rca ys zs O) I
  ≡⟨⟩
    ((I ∷ xs) + ((O ∷ ys) + (I ∷ zs)))
  ∎
add-assocˡ (I ∷ xs) (I ∷ ys) (O ∷ zs) = begin
    (((I ∷ xs) + (I ∷ ys)) + (O ∷ zs))
  ≡⟨⟩
    O ∷ rca (rca xs ys I) zs O
  ≡⟨ cong (λ l → O ∷ rca l zs O) (rca-lift-carry xs ys) ⟩
    O ∷ rca (inc (rca xs ys O)) zs O
  ≡⟨ cong (O ∷_) (rca-lift-incˡ (rca xs ys O) zs) ⟩
    O ∷ inc (rca (rca xs ys O) zs O)
  ≡⟨ cong (λ l → O ∷ inc l) (add-assocˡ xs ys zs) ⟩
    O ∷ inc (rca xs (rca ys zs O) O)
  ≡⟨ cong (O ∷_) (sym (rca-lift-carry xs (rca ys zs O))) ⟩
    O ∷ rca xs (rca ys zs O) I
  ≡⟨⟩
    ((I ∷ xs) + ((I ∷ ys) + (O ∷ zs)))
  ∎
add-assocˡ (I ∷ xs) (I ∷ ys) (I ∷ zs) = begin
    (((I ∷ xs) + (I ∷ ys)) + (I ∷ zs))
  ≡⟨⟩
    I ∷ rca (rca xs ys I) zs O
  ≡⟨ cong (λ l → I ∷ rca l zs O) (rca-lift-carry xs ys) ⟩
    I ∷ rca (inc (rca xs ys O)) zs O
  ≡⟨ cong (λ l → I ∷ rca l zs O) (sym (rca-lift-incʳ xs ys)) ⟩
    I ∷ rca (rca xs (inc ys) O) zs O
  ≡⟨ cong (I ∷_) (add-assocˡ xs (inc ys) zs) ⟩
    I ∷ rca xs (rca (inc ys) zs O) O
  ≡⟨ cong (λ l → I ∷ rca xs l O) (rca-lift-incˡ ys zs) ⟩
    I ∷ rca xs (inc (rca ys zs O)) O
  ≡⟨ cong (λ l → I ∷ rca xs l O) (sym (rca-lift-carry ys zs)) ⟩
    I ∷ rca xs (rca ys zs I) O
  ≡⟨⟩
    ((I ∷ xs) + ((I ∷ ys) + (I ∷ zs)))
  ∎
-- add-assocˡ (x ∷ xs) (y ∷ ys) (z ∷ zs) = begin
--     (((x ∷ xs) + (y ∷ ys)) + (z ∷ zs))
--   ≡⟨⟩
--     ((x xor y xor O) xor z xor O) ∷ (rca (rca xs ys (x ∧ y ∨ O ∧ (x xor y))) zs
--        ((x xor y xor O) ∧ z ∨ O ∧ ((x xor y xor O) xor z)))
--   ≡⟨ cong (λ l → ((x xor y xor O) xor l) ∷ (rca (rca xs ys (x ∧ y ∨ O ∧ (x xor y))) zs
--        ((x xor y xor O) ∧ z ∨ O ∧ ((x xor y xor O) xor z)))) (false-xorʳ z) ⟩
--     ((x xor y xor O) xor z) ∷
--       rca (rca xs ys (x ∧ y ∨ O ∧ (x xor y))) zs
--       ((x xor y xor O) ∧ z ∨ O ∧ ((x xor y xor O) xor z))
--   ≡⟨ cong (λ l → ((x xor l) xor z) ∷ (rca (rca xs ys (x ∧ y ∨ O ∧ (x xor y))) zs
--        ((x xor l) ∧ z ∨ O ∧ ((x xor l) xor z)))) (false-xorʳ y) ⟩
--     ((x xor y) xor z) ∷
--       rca (rca xs ys (x ∧ y ∨ O ∧ (x xor y))) zs
--       ((x xor y) ∧ z ∨ O ∧ ((x xor y) xor z))
--   ≡⟨ cong (λ l → ((x xor y) xor z) ∷ (rca (rca xs ys (x ∧ y ∨ l)) zs
--        ((x xor y) ∧ z ∨ O ∧ ((x xor y) xor z)))) (∧-zeroˡ (x xor y)) ⟩
--     ((x xor y) xor z) ∷
--       rca (rca xs ys (x ∧ y ∨ O)) zs
--       ((x xor y) ∧ z ∨ O ∧ ((x xor y) xor z))
--   ≡⟨ cong (λ l → ((x xor y) xor z) ∷ (rca (rca xs ys (x ∧ y ∨ O)) zs
--        ((x xor y) ∧ z ∨ l))) (∧-zeroˡ ((x xor y) xor z)) ⟩
--     ((x xor y) xor z) ∷
--       rca (rca xs ys (x ∧ y ∨ O)) zs ((x xor y) ∧ z ∨ O)
--   ≡⟨ cong (λ l → ((x xor y) xor z) ∷
--       rca (rca xs ys l) zs ((x xor y) ∧ z ∨ O)) (∨-identityʳ (x ∧ y)) ⟩
--     ((x xor y) xor z) ∷ rca (rca xs ys (x ∧ y)) zs ((x xor y) ∧ z ∨ O)
--   ≡⟨ cong (λ l → ((x xor y) xor z) ∷ rca (rca xs ys (x ∧ y)) zs l) (∨-identityʳ ((x xor y) ∧ z)) ⟩
--     ((x xor y) xor z) ∷ rca (rca xs ys (x ∧ y)) zs ((x xor y) ∧ z)
--   ≡⟨ cong (λ l → ((x xor y) xor z) ∷ rca (rca xs ys (x ∧ y)) zs l) (∧-distribʳ-xor z x y) ⟩
--     ((x xor y) xor z) ∷ rca (rca xs ys (x ∧ y)) zs (x ∧ z xor y ∧ z)
--   ≡⟨ {! cong (((x xor y) xor z) ∷_) (add-assocˡ xs ys zs)  !} ⟩
--     ((x xor y) xor z) ∷ rca xs (rca ys zs (y ∧ z)) (x ∧ y xor x ∧ z)
--   ≡⟨ cong (λ l → ((x xor y) xor z) ∷ rca xs (rca ys zs (y ∧ z)) l) (sym (∧-distribˡ-xor x y z)) ⟩
--     ((x xor y) xor z) ∷ rca xs (rca ys zs (y ∧ z)) (x ∧ (y xor z))
--   ≡⟨ cong (_∷ rca xs (rca ys zs (y ∧ z)) (x ∧ (y xor z))) (xor-assoc x y z) ⟩
--     (x xor (y xor z)) ∷ (rca xs (rca ys zs (y ∧ z)) (x ∧ (y xor z)))
--   ≡⟨ cong (λ l → (x xor (y xor z)) ∷ (rca xs (rca ys zs l)
--        (x ∧ (y xor z)))) (sym (∨-identityʳ (y ∧ z))) ⟩
--     (x xor (y xor z)) ∷ (rca xs (rca ys zs (y ∧ z ∨ O))
--        (x ∧ (y xor z)))
--   ≡⟨ cong (λ l → (x xor (y xor z)) ∷ (rca xs (rca ys zs (y ∧ z ∨ l))
--        (x ∧ (y xor z)))) (sym (∧-zeroˡ (y xor z))) ⟩
--     (x xor (y xor z)) ∷ (rca xs (rca ys zs (y ∧ z ∨ O ∧ (y xor z)))
--        (x ∧ (y xor z)))
--   ≡⟨ cong (λ l → (x xor (y xor z)) ∷ (rca xs (rca ys zs (y ∧ z ∨ O ∧ (y xor z)))
--        l)) (sym (∨-identityʳ (x ∧ (y xor z)))) ⟩
--     (x xor (y xor z)) ∷ (rca xs (rca ys zs (y ∧ z ∨ O ∧ (y xor z)))
--        (x ∧ (y xor z) ∨ O))
--   ≡⟨ cong (λ l → (x xor (y xor z)) ∷ (rca xs (rca ys zs (y ∧ z ∨ O ∧ (y xor z)))
--        (x ∧ (y xor z) ∨ l))) (sym (∧-zeroˡ (x xor y xor z))) ⟩
--     (x xor (y xor z)) ∷ (rca xs (rca ys zs (y ∧ z ∨ O ∧ (y xor z)))
--        (x ∧ (y xor z) ∨ O ∧ (x xor y xor z)))
--   ≡⟨ cong (λ l → (x xor (y xor l)) ∷ (rca xs (rca ys zs (y ∧ z ∨ O ∧ (y xor z)))
--        (x ∧ (y xor l) ∨ O ∧ (x xor y xor l)))) (sym (false-xorʳ z)) ⟩
--     (x xor (y xor z xor O)) ∷ (rca xs (rca ys zs (y ∧ z ∨ O ∧ (y xor z)))
--        (x ∧ (y xor z xor O) ∨ O ∧ (x xor y xor z xor O)))
--   ≡⟨ cong (λ l → (x xor l) ∷ (rca xs (rca ys zs (y ∧ z ∨ O ∧ (y xor z)))
--        (x ∧ (y xor z xor O) ∨ O ∧ (x xor y xor z xor O)))) (sym (false-xorʳ (y xor z xor O))) ⟩
--     (x xor (y xor z xor O) xor O) ∷ (rca xs (rca ys zs (y ∧ z ∨ O ∧ (y xor z)))
--        (x ∧ (y xor z xor O) ∨ O ∧ (x xor y xor z xor O)))
--   ≡⟨⟩
--     ((x ∷ xs) + ((y ∷ ys) + (z ∷ zs)))
--   ∎
     