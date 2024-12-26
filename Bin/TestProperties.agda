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
     