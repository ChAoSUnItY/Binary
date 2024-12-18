module Bin.Base where

open import Relation.Nullary.Decidable using (⌊_⌋; yes; no)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (Bool; true; false; _∨_; _∧_)
                      renaming (not to notᵇ; _xor_ to _xorᵇ_)
open import Data.Vec using (Vec; _∷_; []; drop; take; splitAt; length)
open import Data.Product using (_×_)

pattern I = true
pattern O = false

Bit : Set
Bit = Bool

not : Bit → Bit
not x = notᵇ x

infixr 6 _and_
infixr 5 _or_ _xor_

_or_ : Bit → Bit → Bit
x or y = x ∨ y

_and_ : Bit → Bit → Bit
x and y = x ∧ y

_xor_ : Bit → Bit → Bit
x xor y = x xorᵇ y

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

-- TODO: Maybe don't discard carry?
-- Adds 2 binary number, may cause overflow
add : ∀ {n} → Binary n → Binary n → Binary n
add xs ys = add' xs ys O
  where
    add' : ∀ {n} → Binary n → Binary n → Bit → Binary n
    add' []       []       _     = []
    add' (x ∷ xs) (y ∷ ys) carry with x | y | carry
    ...                          | O | O | O = O ∷ add' xs ys O
    ...                          | O | O | I = I ∷ add' xs ys O
    ...                          | I | I | O = O ∷ add' xs ys I
    ...                          | I | I | I = I ∷ add' xs ys I
    ...                          | _ | _ | O = I ∷ add' xs ys O
    ...                          | _ | _ | I = O ∷ add' xs ys I

-- Increment by 1
inc : ∀ {n} → Binary n → Binary n
inc []       = []
inc (O ∷ xs) = I ∷ xs
inc (I ∷ xs) = O ∷ inc xs

-- Decrement by 1
dec : ∀ {n} → Binary n → Binary n
dec []       = []
dec (O ∷ xs) = I ∷ dec xs
dec (I ∷ xs) = O ∷ xs

-- Bitwise negation
~_ : ∀ {n} → Binary n → Binary n
~ []       = []
~ (x ∷ xs) = not x ∷ ~ xs

-- Negation, which converts binary by two's complement
-_ : ∀ {n} → Binary n → Binary n
- []       = []
- (x ∷ xs) = inc (~ (x ∷ xs))

-- Bitwise and
_&_ : ∀ {n} → Binary n → Binary n → Binary n
[] & []             = []
(x ∷ xs) & (y ∷ ys) = (x and y) ∷ (xs & ys)

-- Bitwise or
_∥_ : ∀ {n} → Binary n → Binary n → Binary n
[] ∥ []             = []
(x ∷ xs) ∥ (y ∷ ys) = (x or y) ∷ (xs ∥ ys)

-- Bitwise exclusive or
_^_ : ∀ {n} → Binary n → Binary n → Binary n
[] ^ []             = []
(x ∷ xs) ^ (y ∷ ys) = (x xor y) ∷ (xs ^ ys)

-- Logical left shift by 1
_<<ᴸ1 : ∀ {n} → Binary n → Binary n
[]       <<ᴸ1 = []
(x ∷ xs) <<ᴸ1 = O ∷ dropLast (x ∷ xs)

-- Logical right shift by 1
_>>ᴸ1 : ∀ {n} → Binary n → Binary n
[]       >>ᴸ1 = []
(_ ∷ xs) >>ᴸ1 = append xs O

-- ^-swap : ∀ {n} → Binary n × Binary n → 

-- Nat-Binary conversions
ℕ⇒Binary : (d n : ℕ) → Binary n
ℕ⇒Binary 0 n       = zeroᴮ n
ℕ⇒Binary (suc d) n = inc (ℕ⇒Binary d n)

-- Binary-Nat conversion, binary would be treated as unsigned
Binary⇒ℕ : ∀ {n} → Binary n → ℕ
Binary⇒ℕ []       = 0
Binary⇒ℕ (x ∷ xs) with x
...               | O = 2 * Binary⇒ℕ xs
...               | I = 1 + 2 * Binary⇒ℕ xs
 