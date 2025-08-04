module Bin.SignedProperties where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; cong-app; subst; trans; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; 2+; _>_; s<s)
open import Data.Bool using (_∧_; _∨_; not; _xor_)
open import Data.Vec using (Vec; _∷_; [])
open import Bin.Base
open import Bin.Properties

inc-signed-max≡signed-min : ∀ {n} {h : n > 0} → inc (signed-max n {h}) ≡ signed-min n {h}
inc-signed-max≡signed-min {suc 0} = refl
inc-signed-max≡signed-min {2+ n} {h} =
  begin
    inc (signed-max (2+ n) {h})
  ≡⟨⟩
    inc (I ∷ (signed-max (suc n)))
  ≡⟨⟩
    O ∷ inc (signed-max (suc n))
  ≡⟨ cong (O ∷_) inc-signed-max≡signed-min ⟩
    O ∷ signed-min (suc n)
  ∎

signed-max+signed-min≡negative-one : ∀ {n} {h : n > 0} → (signed-max n {h}) + (signed-min n {h}) ≡ - (oneᴮ n)
signed-max+signed-min≡negative-one {suc 0} = refl
signed-max+signed-min≡negative-one {2+ n} {h} = 
  begin
    (signed-max (2+ n) {h}) + (signed-min (2+ n) {h})
  ≡⟨⟩
    (I ∷ (signed-max (suc n))) + (O ∷ signed-min (suc n))
  ≡⟨⟩
    I ∷ (signed-max (suc n)) + (signed-min (suc n))
  ≡⟨ cong (I ∷_) signed-max+signed-min≡negative-one ⟩
    I ∷ (- oneᴮ (suc n))
  ≡⟨⟩
    - oneᴮ (2+ n)
  ∎

negate-signed-min≡signed-min : ∀ {n} {h : n > 0} → - (signed-min n {h}) ≡ signed-min n {h}
negate-signed-min≡signed-min {suc 0} = refl
negate-signed-min≡signed-min {2+ n} {h} =
  begin
    - signed-min (2+ n) {h}
  ≡⟨⟩
    inc (~ (O ∷ signed-min (suc n)))
  ≡⟨⟩
    inc (I ∷ ~ signed-min (suc n))
  ≡⟨⟩
    O ∷ inc (~ signed-min (suc n))
  ≡⟨ cong (O ∷_) (negate≡inc-~ (signed-min (suc n))) ⟩
    O ∷ (- signed-min (suc n))
  ≡⟨ cong (O ∷_) negate-signed-min≡signed-min ⟩
    O ∷ signed-min (suc n)
  ≡⟨⟩
    signed-min (2+ n) {h}
  ∎
