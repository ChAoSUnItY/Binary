module Binary.Comparison.Base where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; _∷_; []; last)
open import Binary.Base

-- Bit comparison
data _<bᵘ_ : Bit → Bit → Set where
  lt : O <bᵘ I

_≤bᵘ_ : Bit → Bit → Set
x ≤bᵘ y = (x <bᵘ y) ⊎ (x ≡ y)

data _>bᵘ_ : Bit → Bit → Set where
  gt : I >bᵘ O

_≥bᵘ_ : Bit → Bit → Set
x ≥bᵘ y = (x >bᵘ y) ⊎ (x ≡ y)

instance
  inst-gt : I >bᵘ O
  inst-gt = gt

  inst-lt : O <bᵘ I
  inst-lt = lt
  
  inst-le-OO : O ≤bᵘ O
  inst-le-OO = inj₂ refl

  inst-le-II : I ≤bᵘ I
  inst-le-II = inj₂ refl

  inst-le-OI : O ≤bᵘ I
  inst-le-OI = inj₁ lt

-- Unsigned comparison
data _<ᵘ_ : ∀ {n} → Binary (suc n) → Binary (suc n) → Set where
  lt-tail : ∀ {n} {x y : Bit} {xs ys : Binary (suc n)}
          → xs <ᵘ ys 
          → (x ∷ xs) <ᵘ (y ∷ ys)
  lt-head : ∀ {n} {x y : Bit} {xs ys : Binary n}
          → xs ≡ ys 
          → x <bᵘ y 
          → (x ∷ xs) <ᵘ (y ∷ ys)

_≤ᵘ_ : ∀ {n} → Binary (suc n) → Binary (suc n) → Set
xs ≤ᵘ ys = (xs <ᵘ ys) ⊎ (xs ≡ ys)  

_>ᵘ_ : ∀ {n} → Binary (suc n) → Binary (suc n) → Set
xs >ᵘ ys = ¬(xs ≤ᵘ ys)

_≥ᵘ_ : ∀ {n} → Binary (suc n) → Binary (suc n) → Set
xs ≥ᵘ ys = ¬(xs <ᵘ ys)

AddNotOverflow : ∀ {n} → Binary (suc n) → Binary (suc n) → Set
AddNotOverflow xs ys = ys ≤ᵘ (~ xs)

AddOverflow : ∀ {n} → Binary (suc n) → Binary (suc n) → Set
AddOverflow xs ys = ys >ᵘ (~ xs)

AddNotMax : ∀ {n} → Binary (suc n) → Binary (suc n) → Set
AddNotMax xs ys = ys <ᵘ (~ xs)

-- Signed comparison
signBit : ∀ {n} → Binary (suc n) → Bit
signBit = last

_<_ : ∀ {n} → Binary (suc n) → Binary (suc n) → Set
xs < ys with signBit xs | signBit ys
... | I | O = ⊤
... | O | I = ⊥
... | _ | _ = xs <ᵘ ys

_≤_ : ∀ {n} → Binary (suc n) → Binary (suc n) → Set
xs ≤ ys = xs < ys ⊎ xs ≡ ys

_>_ : ∀ {n} → Binary (suc n) → Binary (suc n) → Set
xs > ys = ¬(xs ≤ ys)

_≥_ : ∀ {n} → Binary (suc n) → Binary (suc n) → Set
xs ≥ ys = ¬(xs < ys)

