module Bin.Base where

open import Relation.Nullary.Decidable using (⌊_⌋; yes; no)
open import Data.Nat using (ℕ; zero; suc)
                     renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Bool using (Bool; true; false; not; _∨_; _∧_; _xor_)
open import Data.Vec using (Vec; _∷_; []; drop; take; splitAt; length)
open import Data.Product using (uncurry; _,_; _×_)

pattern I = true
pattern O = false

Bit : Set
Bit = Bool

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
oneᴮ : ∀ (n : ℕ) → Binary n
oneᴮ 0       = []
oneᴮ (suc n) = I ∷ (zeroᴮ n)

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
(x ∷ xs) & (y ∷ ys) = (x ∧ y) ∷ (xs & ys)

-- Bitwise or
_∥_ : ∀ {n} → Binary n → Binary n → Binary n
[] ∥ []             = []
(x ∷ xs) ∥ (y ∷ ys) = (x ∨ y) ∷ (xs ∥ ys)

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

-- Ripple carry add simulation
rca : ∀ {n} → Binary n → Binary n → Bit → Binary n
rca []       []       _     = []
rca (x ∷ xs) (y ∷ ys) carry = (x xor y xor carry) ∷ rca xs ys ((x ∧ y) ∨ (carry ∧ (x xor y)))

rca¹ : ∀ {n} → Binary n → Binary n → Bit → Binary n × Bit
rca¹ []  [] c = [] , c
rca¹ (x ∷ xs) (y ∷ ys) carry using carry' ← ((x ∧ y) ∨ (carry ∧ (x xor y)))
                             with rca¹ xs ys carry'
... | (tail , carry'') = ((x xor y xor carry) ∷ tail) , carry''

-- TODO: Maybe don't discard carry?
-- Adds 2 binary number, may cause overflow
add : ∀ {n} → Binary n → Binary n → Binary n
add xs ys = rca xs ys O

_+_ : ∀ {n} → Binary n → Binary n → Binary n
xs + ys = add xs ys

sub : ∀ {n} → Binary n → Binary n → Binary n
sub xs ys = add xs (- ys)

_-_ : ∀ {n} → Binary n → Binary n → Binary n
xs - ys = sub xs ys

-- ^-swap : ∀ {n} → Binary n × Binary n → 

-- Nat-Binary conversions
ℕ⇒Binary : (d n : ℕ) → Binary n
ℕ⇒Binary 0 n       = zeroᴮ n
ℕ⇒Binary (suc d) n = inc (ℕ⇒Binary d n)

-- Binary-Nat conversion, binary would be treated as unsigned
Binary⇒ℕ : ∀ {n} → Binary n → ℕ
Binary⇒ℕ []       = 0
Binary⇒ℕ (x ∷ xs) with x
...               | O = 2 *ℕ Binary⇒ℕ xs
...               | I = 1 +ℕ 2 *ℕ Binary⇒ℕ xs
  