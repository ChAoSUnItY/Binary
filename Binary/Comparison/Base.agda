module Binary.Comparison.Base where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; _∷_; [])
open import Binary.Base

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

data _<ᵘ_ : ∀ {n} → Binary n → Binary n → Set where
  lt-tail : ∀ {n} {x y : Bit} {xs ys : Binary n}
          → xs <ᵘ ys 
          → (x ∷ xs) <ᵘ (y ∷ ys)
  lt-head : ∀ {n} {x y : Bit} {xs ys : Binary n}
          → xs ≡ ys 
          → x <bᵘ y 
          → (x ∷ xs) <ᵘ (y ∷ ys)

_≤ᵘ_ : ∀ {n} → Binary n → Binary n → Set
xs ≤ᵘ ys = (xs <ᵘ ys) ⊎ (xs ≡ ys)  

_>ᵘ_ : ∀ {n} → Binary n → Binary n → Set
xs >ᵘ ys = ¬(xs ≤ᵘ ys)

_≥ᵘ_ : ∀ {n} → Binary n → Binary n → Set
xs ≥ᵘ ys = ¬(xs <ᵘ ys)

AddNotOverflow : ∀ {n} → Binary n → Binary n → Set
AddNotOverflow xs ys = ys ≤ᵘ (~ xs)

AddOverflow : ∀ {n} → Binary n → Binary n → Set
AddOverflow xs ys = ys >ᵘ (~ xs)

AddNotMax : ∀ {n} → Binary n → Binary n → Set
AddNotMax xs ys = ys <ᵘ (~ xs)
