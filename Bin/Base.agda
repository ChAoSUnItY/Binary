module Bin.Base where

open import Relation.Nullary.Decidable using (⌊_⌋; yes; no)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (Bool; true; false; not)
open import Data.Vec using (Vec; _∷_; []; drop; take; splitAt; length)

data Bit : Set where
  O : Bit
  I : Bit

negate : Bit → Bit
negate O = I
negate I = O

-- In this case, we simluate the binary operations
-- in big endian to best fit Vec's data structure.
Binary : ℕ → Set
Binary n = Vec Bit n

zeroᴮ : ∀ (n : ℕ) → Binary n
zeroᴮ 0       = []
zeroᴮ (suc n) = O ∷ (zeroᴮ n)

onesᴮ : ∀ (n : ℕ) → Binary n
onesᴮ 0       = []
onesᴮ (suc n) = I ∷ (onesᴮ n)

append : ∀ {n} → Binary n → Bit → Binary (suc n)
append []       x = x ∷ []
append (y ∷ ys) x = y ∷ append ys x

dropLast : ∀ {n} → Binary (suc n) → Binary n
dropLast (x ∷ [])     = []
dropLast (x ∷ y ∷ xs) = x ∷ dropLast (y ∷ xs)

_==_ : ∀ {n} → Binary n → Binary n → Bool
[] == [] = true
(x ∷ xs) == (y ∷ ys) with x | y
...                  | O | O = xs == ys
...                  | I | I = xs == ys
...                  | _ | _ = false

_≠_ : ∀ {n} → Binary n → Binary n → Bool
xs ≠ ys = not (xs == ys)

flip : ∀ {n} → Binary n → Binary n
flip [] = []
flip (x ∷ xs) = negate x ∷ flip xs

-- Adds 2 binary number, may cause overflow
add : ∀ {n} → Binary n → Binary n → Binary n
add xs ys = add' xs ys false
  where
    add' : ∀ {n} → Binary n → Binary n → (carry : Bool) → Binary n
    add' []       []       _     = []
    add' (x ∷ xs) (y ∷ ys) carry with x | y | carry
    ...                          | O | O | false = O ∷ add' xs ys false
    ...                          | O | O | true  = I ∷ add' xs ys false
    ...                          | I | I | false = O ∷ add' xs ys true
    ...                          | I | I | true  = I ∷ add' xs ys true
    ...                          | _ | _ | false = I ∷ add' xs ys false
    ...                          | _ | _ | true  = O ∷ add' xs ys true

-- Increment by 1
inc : ∀ {n} → Binary n → Binary n
inc []       = []
inc (O ∷ xs) = I ∷ xs
inc (I ∷ xs) = O ∷ inc xs

-- Decrement by 1
dec : ∀ {n} → Binary n → Binary n
dec [] = []
dec (O ∷ xs) = I ∷ dec xs
dec (I ∷ xs) = O ∷ xs

-- Converts to two complement
twoComplement : ∀ {n} → Binary n → Binary n
twoComplement [] = []
twoComplement (x ∷ xs) = inc (flip (x ∷ xs))

-- Logical left shift by 1
_<<ᴸ1 : ∀ {n} → Binary n → Binary n
[]       <<ᴸ1 = []
(x ∷ xs) <<ᴸ1 = O ∷ dropLast (x ∷ xs)

-- Logical right shift by 1
_>>ᴿ1 : ∀ {n} → Binary n → Binary n
[]       >>ᴿ1 = []
(_ ∷ xs) >>ᴿ1 = append xs O

-- Nat-Binary conversions
toBinary : (d n : ℕ) → Binary n
toBinary 0 n = zeroᴮ n
toBinary (suc d) n = inc (toBinary d n)

fromBinary : ∀ {n} → Binary n → ℕ
fromBinary []       = 0
fromBinary (x ∷ xs) with x
...                 | O = 2 * fromBinary xs
...                 | I = 1 + 2 * fromBinary xs