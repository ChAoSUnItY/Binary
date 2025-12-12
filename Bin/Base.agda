module Bin.Base where

open import Data.Nat using (ℕ; suc)
open import Data.Bool using (Bool; true; false; not; _∨_; _∧_; _xor_)
open import Data.Vec using (Vec; _∷_; []; replicate; map; zipWith)
open import Data.Bool using (Bool; true; false; not)

pattern I = true
pattern O = false

Bit : Set
Bit = Bool

-- In this case, we simluate the binary operations
-- in big endian to best fit Vec's data structure.
--
-- For example, for a normalized binary representation
-- O ∷ I ∷ O ∷ O ∷ [], it represents a binary with 4 bits
-- and represents decimal value 2.
Binary : ℕ → Set
Binary n = Vec Bit n

-- Helper functions to create basic binary numbers
zero : (n : ℕ) → Binary n
zero n = replicate n O

ones : (n : ℕ) → Binary n
ones n = replicate n I

-- Carryless operations
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
~_ = map not

-- Negation, which converts binary by two's complement
-_ : ∀ {n} → Binary n → Binary n
- xs = inc (~ xs)

-- Bitwise and
_&_ : ∀ {n} → Binary n → Binary n → Binary n
_&_ = zipWith (_∧_)

-- Bitwise or
_∥_ : ∀ {n} → Binary n → Binary n → Binary n
_∥_ = zipWith (_∨_)

-- Bitwise exclusive or
_^_ : ∀ {n} → Binary n → Binary n → Binary n
_^_ = zipWith (_xor_)

-- Bitwise exclusive NOR
_xnor_ : Bit → Bit → Bit
O xnor y = not y
I xnor y = y

_==_ : ∀ {n} → Binary n → Binary n → Binary n
_==_ = zipWith (_xnor_)

-- Ripple carry add simulation
rca : ∀ {n} → Binary n → Binary n → Bit → Binary n
rca []       []       _     = []
rca (x ∷ xs) (y ∷ ys) carry = ((x xor y) xor carry) ∷ rca xs ys ((x ∧ y) ∨ (carry ∧ (x xor y)))

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
