module Binary.Signed where

open import Data.Nat using (ℕ; suc)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; _xor_)
open import Data.Vec using (Vec; _∷_; []; replicate; map; zipWith; last)
open import Relation.Binary using (Rel)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)

open import Binary.Base
open import Binary.Comparison.Base using (_<ᵘ_; _≤ᵘ_; _>ᵘ_; _≥ᵘ_)

-- Signed binary number representation using Two's Complement.
-- We enforce that the binary number must have at least 1 bit (the sign bit).
-- The underlying representation is the same as Binary (Little Endian),
-- so arithmetic operations can be reused directly.
data Signed (n : ℕ) : Set where
  signed : Binary (suc n) → Signed n

-- Unwraps the signed number to get the raw binary bits
getValue : ∀ {n} → Signed n → Binary (suc n)
getValue (signed xs) = xs

-- Extracts the Most Significant Bit (Sign Bit).
-- Since Binary is Little Endian, the last bit is the MSB.
signBit : ∀ {n} → Signed n → Bit
signBit (signed xs) = last xs

-- Checks if the number is negative (MSB == I)
isNegative : ∀ {n} → Signed n → Bool
isNegative s with signBit s
... | O = false
... | I = true

-- Signed Comparison
-- Logic:
-- If signs differ, Negative < Positive.
-- If signs are same, compare as Unsigned (Binary's <ᵘ handles this correctly for 2's complement).
_<ˢ_ : ∀ {n} → Signed n → Signed n → Set
xs <ˢ ys with signBit xs | signBit ys
... | I | O = ⊤              -- Neg < Pos : True
... | O | I = ⊥              -- Pos < Neg : False
... | _ | _ = getValue xs <ᵘ getValue ys

_≤ˢ_ : ∀ {n} → Signed n → Signed n → Set
xs ≤ˢ ys with signBit xs | signBit ys
... | I | O = ⊤
... | O | I = ⊥
... | _ | _ = getValue xs ≤ᵘ getValue ys

_>ˢ_ : ∀ {n} → Signed n → Signed n → Set
xs >ˢ ys = ys <ˢ xs

_≥ˢ_ : ∀ {n} → Signed n → Signed n → Set
xs ≥ˢ ys = ys ≤ˢ xs

-- Arithmetic Lifting (Modular Arithmetic matches Two's Complement)

_+ˢ_ : ∀ {n} → Signed n → Signed n → Signed n
signed xs +ˢ signed ys = signed (xs + ys)

_-ˢ_ : ∀ {n} → Signed n → Signed n → Signed n
signed xs -ˢ signed ys = signed (xs - ys)

_&ˢ_ : ∀ {n} → Signed n → Signed n → Signed n
signed xs &ˢ signed ys = signed (xs & ys)

_∥ˢ_ : ∀ {n} → Signed n → Signed n → Signed n
signed xs ∥ˢ signed ys = signed (xs ∥ ys)

_^ˢ_ : ∀ {n} → Signed n → Signed n → Signed n
signed xs ^ˢ signed ys = signed (xs ^ ys)

negateˢ : ∀ {n} → Signed n → Signed n
negateˢ (signed xs) = signed (- xs)

absˢ : ∀ {n} → Signed n → Signed n
absˢ s with isNegative s
... | true  = negateˢ s
... | false = s
