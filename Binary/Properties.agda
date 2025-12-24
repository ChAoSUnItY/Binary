module Binary.Properties where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; cong-app; subst; trans; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Vec using (Vec; _∷_; []; _++_; map; last; drop; take; replicate; cast; [_])
open import Data.Vec.Properties
open import Data.Vec.Relation.Binary.Equality.Cast
open import Data.Nat using (ℕ; suc; _≤_; z≤n; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; +-suc; +-comm; +-assoc)
open import Data.Bool using (_∧_; _∨_; not; _xor_)
open import Data.Bool.Properties hiding (≤-refl)
open import Function.Base
open import Binary.Base

-- Base definition
cons-inj : ∀ {n} {x y : Bit} {xs ys : Binary n} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
cons-inj refl = refl

-- Negation properties
~-involutive : ∀ {n} (xs : Binary n) → ~ (~ xs) ≡ xs
~-involutive xs = begin
    ~ (~ xs)
  ≡⟨⟩
    map not (map not xs)
  ≡⟨ sym (map-∘ _ _ _) ⟩
    map (not ∘ not) xs
  ≡⟨ map-cong (not-involutive) _ ⟩
    map id xs
  ≡⟨ map-id _ ⟩
    xs
  ∎

~-zero≡ones : ∀ {n} → ~ (zero n) ≡ ones n
~-zero≡ones {ℕ.zero} = refl
~-zero≡ones {suc n} rewrite ~-zero≡ones {n} = refl

~-ones≡zero : ∀ {n} → ~ (ones n) ≡ zero n
~-ones≡zero {ℕ.zero} = refl
~-ones≡zero {suc n} rewrite ~-ones≡zero {n} = refl

-- 2's complement properties
nneg-involutive : ∀ {n} (xs : Binary n) → - (- xs) ≡ xs
nneg-involutive [] = refl
nneg-involutive (x ∷ xs) with x
... | O = begin
    inc (~ (inc (~ (O ∷ xs))))
  ≡⟨⟩
    O ∷ - (- xs)
  ≡⟨ cong (O ∷_) (nneg-involutive xs) ⟩
    O ∷ xs
  ∎
... | I = begin
    inc (~ (inc (~ (I ∷ xs))))
  ≡⟨⟩
    I ∷ ~ (~ xs)
  ≡⟨ cong (I ∷_) (~-involutive xs) ⟩
    I ∷ xs
  ∎

nneg-zero≡zero : ∀ {n} → - (zero n) ≡ zero n
nneg-zero≡zero {ℕ.zero} = refl
nneg-zero≡zero {suc n} rewrite nneg-zero≡zero {n} = refl

nneg-ones≡inc-zero : ∀ {n} → - (ones n) ≡ inc (zero n)
nneg-ones≡inc-zero {n} rewrite ~-ones≡zero {n} = refl

-- increment / decrement properties
inc-ones≡zero : ∀ {n} → inc (ones n) ≡ zero n
inc-ones≡zero {ℕ.zero} = refl
inc-ones≡zero {suc n} rewrite inc-ones≡zero {n} = refl

dec-zero≡ones : ∀ {n} → dec (zero n) ≡ ones n
dec-zero≡ones {ℕ.zero} = refl
dec-zero≡ones {suc n} rewrite dec-zero≡ones {n} = refl

inc-inj : ∀ {n} {xs ys : Binary n} → inc xs ≡ inc ys → xs ≡ ys
inc-inj {_} {[]} {[]} = id
inc-inj {suc n} {O ∷ xs} {I ∷ ys} ()
inc-inj {suc n} {I ∷ xs} {O ∷ ys} () 
inc-inj {suc n} {x ∷ xs} {y ∷ ys} h with x | y
... | O | O = cong (O ∷_) (cons-inj h)
... | I | I = cong (I ∷_) (inc-inj (cons-inj h))

dec-inj : ∀ {n} {xs ys : Binary n} → dec xs ≡ dec ys → xs ≡ ys
dec-inj {_} {[]} {[]} = id
dec-inj {suc n} {O ∷ xs} {I ∷ ys} ()
dec-inj {suc n} {I ∷ xs} {O ∷ ys} () 
dec-inj {suc n} {x ∷ xs} {y ∷ ys} h with x | y
... | O | O = cong (O ∷_) (dec-inj (cons-inj h))
... | I | I = cong (I ∷_) (cons-inj h)

inc-dec-elim : ∀ {n} (xs : Binary n) → inc (dec xs) ≡ xs
inc-dec-elim [] = refl
inc-dec-elim (x ∷ xs) with x
... | O = begin
    inc (dec (O ∷ xs))
  ≡⟨⟩
    O ∷ inc (dec xs)
  ≡⟨ cong (O ∷_) (inc-dec-elim xs) ⟩
    O ∷ xs
  ∎
... | I = refl

dec-inc-elim : ∀ {n} (xs : Binary n) → dec (inc xs) ≡ xs
dec-inc-elim [] = refl
dec-inc-elim (x ∷ xs) with x
... | O = refl
... | I = begin
    dec (inc (I ∷ xs))
  ≡⟨⟩
    I ∷ dec (inc xs)
  ≡⟨ cong (I ∷_) (dec-inc-elim xs) ⟩
    I ∷ xs
  ∎

-- or properties
∥-assoc : ∀ {n} (xs ys zs : Binary n) → (xs ∥ ys) ∥ zs ≡ xs ∥ (ys ∥ zs)
∥-assoc = zipWith-assoc (∨-assoc)

∥-comm : ∀ {n} (xs ys : Binary n) → xs ∥ ys ≡ ys ∥ xs
∥-comm = zipWith-comm (∨-comm)

∥-identityˡ : ∀ {n} (xs : Binary n) → zero n ∥ xs ≡ xs
∥-identityˡ = zipWith-identityˡ (∨-identityˡ)

∥-identityʳ : ∀ {n} (xs : Binary n) → xs ∥ zero n ≡ xs
∥-identityʳ = zipWith-identityʳ (∨-identityʳ)

∥-zeroˡ : ∀ {n} (xs : Binary n) → ones n ∥ xs ≡ ones n
∥-zeroˡ = zipWith-zeroˡ (∨-zeroˡ)

∥-zeroʳ : ∀ {n} (xs : Binary n) → xs ∥ ones n ≡ ones n
∥-zeroʳ = zipWith-zeroʳ (∨-zeroʳ)

∥-inverseˡ : ∀ {n} (xs : Binary n) → (~ xs) ∥ xs ≡ ones n
∥-inverseˡ = zipWith-inverseˡ (∨-inverseˡ)

∥-inverseʳ : ∀ {n} (xs : Binary n) → xs ∥ (~ xs) ≡ ones n
∥-inverseʳ = zipWith-inverseʳ (∨-inverseʳ)

∥-idem : ∀ {n} (xs : Binary n) → xs ∥ xs ≡ xs
∥-idem = zipWith-idem (∨-idem)

-- and properties
&-assoc : ∀ {n} (xs ys zs : Binary n) → (xs & ys) & zs ≡ xs & (ys & zs)
&-assoc = zipWith-assoc (∧-assoc)

&-comm : ∀ {n} (xs ys : Binary n) → xs & ys ≡ ys & xs
&-comm = zipWith-comm (∧-comm)

&-identityˡ : ∀ {n} (xs : Binary n) → ones n & xs ≡ xs
&-identityˡ = zipWith-identityˡ (∧-identityˡ)

&-identityʳ : ∀ {n} (xs : Binary n) → xs & ones n ≡ xs
&-identityʳ = zipWith-identityʳ (∧-identityʳ)

&-zeroˡ : ∀ {n} (xs : Binary n) → zero n & xs ≡ zero n
&-zeroˡ = zipWith-zeroˡ (∧-zeroˡ)

&-zeroʳ : ∀ {n} (xs : Binary n) → xs & zero n ≡ zero n
&-zeroʳ = zipWith-zeroʳ (∧-zeroʳ)

&-inverseˡ : ∀ {n} (xs : Binary n) → (~ xs) & xs ≡ zero n
&-inverseˡ = zipWith-inverseˡ (∧-inverseˡ)

&-inverseʳ : ∀ {n} (xs : Binary n) → xs & (~ xs) ≡ zero n
&-inverseʳ = zipWith-inverseʳ (∧-inverseʳ)

&-idem : ∀ {n} (xs : Binary n) → xs & xs ≡ xs
&-idem = zipWith-idem (∧-idem)

-- xor properties
^-assoc : ∀ {n} (xs ys zs : Binary n) → (xs ^ ys) ^ zs ≡ xs ^ (ys ^ zs)
^-assoc = zipWith-assoc (xor-assoc)

^-comm : ∀ {n} (xs ys : Binary n) → xs ^ ys ≡ ys ^ xs
^-comm = zipWith-comm (xor-comm)

^-identityˡ : ∀ {n} (xs : Binary n) → zero n ^ xs ≡ xs
^-identityˡ = zipWith-identityˡ (xor-identityˡ)

^-identityʳ : ∀ {n} (xs : Binary n) → xs ^ zero n ≡ xs
^-identityʳ = zipWith-identityʳ (xor-identityʳ)

^-inverseˡ : ∀ {n} (xs : Binary n) → (~ xs) ^ xs ≡ ones n
^-inverseˡ = zipWith-inverseˡ (xor-inverseˡ)

^-inverseʳ : ∀ {n} (xs : Binary n) → xs ^ (~ xs) ≡ ones n
^-inverseʳ = zipWith-inverseʳ (xor-inverseʳ)

^-onesˡ : ∀ {n} (xs : Binary n) → ones n ^ xs ≡ ~ xs
^-onesˡ [] = refl
^-onesˡ (x ∷ xs) rewrite ^-onesˡ xs = refl

^-onesʳ : ∀ {n} (xs : Binary n) → xs ^ ones n ≡ ~ xs
^-onesʳ [] = refl
^-onesʳ (x ∷ xs) rewrite ^-onesʳ xs | xor-comm x I | true-xor x = refl

^-same : ∀ {n} (xs : Binary n) → xs ^ xs ≡ zero n
^-same [] = refl
^-same (x ∷ xs) rewrite ^-same xs | xor-same x = refl

-- Shift properties
>>ˢ-signbit : ∀ {n} (xs : Binary (suc n)) → xs >>ˢ n ≡ replicate (suc n) (last xs)
>>ˢ-signbit {n} xs = 
  begin
    drop n (cast (+-comm (suc n) n) (xs ++ replicate n (last xs)))
  ≡⟨ drop-++-distrubʳ xs (replicate n (last xs)) ⟩
    drop n (cast (+-comm _ n) xs) ++ replicate n (last xs)
  ≡⟨ cong (_++ replicate n (last xs)) (drop-last xs) ⟩
    (last xs ∷ []) ++ replicate n (last xs)
  ≡⟨⟩
    replicate (suc n) (last xs)
  ∎
  where
    drop-++-distrubʳ : ∀ {n k} (xs : Binary (suc n)) (ys : Binary k) 
                     → drop n (cast (sym (+-suc n k)) (xs ++ ys)) ≡ drop n (cast (+-comm _ n) xs) ++ ys
    drop-++-distrubʳ {ℕ.zero} {_} (x ∷ []) ys rewrite cast-is-id refl ys = refl
    drop-++-distrubʳ {suc n}  {_} (x ∷ xs) ys = drop-++-distrubʳ xs ys

    drop-last : ∀ {n} (xs : Binary (suc n)) → drop n (cast (+-comm _ n) xs) ≡ [ last xs ]
    drop-last {ℕ.zero} (x ∷ []) = refl
    drop-last {suc n} (x ∷ xs) = drop-last xs

-- Misc properties
∧-true-implies-xor-false : (x y : Bit) (h1 : x ∧ y ≡ I) → x xor y ≡ O
∧-true-implies-xor-false O _ ()
∧-true-implies-xor-false I O ()
∧-true-implies-xor-false I I _ = refl
