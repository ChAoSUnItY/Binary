module Bin.Base where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl)
open import Data.Nat using (ℕ; zero; suc; 2+; _>_; s<s; z<s)
                     renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Bool using (Bool; true; false; not; _∨_; _∧_; _xor_)
open import Data.Vec using (Vec; _∷_; []; _++_; zip; drop; take; splitAt; length)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂; map₁)
open import Data.Bool.Base using (Bool; true; false; T; not)
open import Function using (const; _∘_)

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

-- Definitions for signed number signess predicates, notice 
-- that these definitions do not consider 0-bit binary to be
-- either negative or positive binary under 2's complement
-- system, which is meaningless in this case.
interleaved mutual
  negative : ∀ {n} → Binary (suc n) → Bool
  positive : ∀ {n} → Binary (suc n) → Bool

  record SignedNegative {n} (xs : Binary (suc n)) : Set where
    field
      signedNegative : T (negative xs)

  record SignedPositive {n} (xs : Binary (suc n)) : Set where
    field
      signedPositive : T (positive xs)

  instance
    signedNegative : ∀ {n} {xs : Binary (suc n)} {h : T (negative xs)} → SignedNegative xs
    signedNegative {_} {_} {h} = record { signedNegative = h }

  instance
    signedPositive : ∀ {n} {xs : Binary (suc n)} {h : T (positive xs)} → SignedPositive xs
    signedPositive {_} {_} {h} = record { signedPositive = h }

  negative (O ∷ []) = false
  positive (O ∷ []) = true

  negative (I ∷ []) = true
  positive (I ∷ []) = false

  negative (x ∷ x' ∷ xs) = negative (x' ∷ xs)
  positive (x ∷ x' ∷ xs) = positive (x' ∷ xs)

zeroᴮ : ∀ (n : ℕ) → Binary n
zeroᴮ 0       = []
zeroᴮ (suc n) = O ∷ (zeroᴮ n)

onesᴮ : ∀ (n : ℕ) → Binary n
onesᴮ 0       = []
onesᴮ (suc n) = I ∷ (onesᴮ n)

oneᴮ : ∀ (n : ℕ) → Binary n
oneᴮ 0       = []
oneᴮ (suc n) = I ∷ (zeroᴮ n)

signed-max : ∀ (n : ℕ) {_ : n > 0} → Binary n
signed-max (suc 0) = (O ∷ [])
signed-max (2+ n) = I ∷ (signed-max (suc n) {z<s})

signed-min : ∀ (n : ℕ) {_ : n > 0} → Binary n
signed-min (suc 0) = I ∷ []
signed-min (2+ n) = O ∷ (signed-min (suc n) {z<s})

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

-- Extending functions

-- Zero extending
zext : ∀ {n} → Binary n → (m : ℕ) → Binary m
zext []       zero    = []
zext (_ ∷ _)  zero    = []
zext []       (suc m) = O ∷ zext [] m
zext (x ∷ xs) (suc m) = x ∷ zext xs m

-- Sign extending
sext' : ∀ {n} → Binary n → Bit → (m : ℕ) → Binary m
sext' []            _  zero    = []
sext' (_ ∷ [])      _  zero    = []
sext' (_ ∷ _ ∷ _)   _  zero    = []
sext' []            sb (suc m) = sb ∷ sext' [] sb m
sext' (x ∷ [])      _  (suc m) = x ∷ sext' [] x m
sext' (x ∷ xs)      _  (suc m) = x ∷ sext' xs O m

sext : ∀ {n} → Binary n → (m : ℕ) → Binary m
sext xs m = sext' xs O m

-- Ripple carry add simulation
rca : ∀ {n} → Binary n → Binary n → Bit → Binary n
rca []       []       _     = []
rca (x ∷ xs) (y ∷ ys) carry = (x xor y xor carry) ∷ rca xs ys ((x ∧ y) ∨ (carry ∧ (x xor y)))

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
