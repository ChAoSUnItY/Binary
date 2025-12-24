module Binary.HackersDelight.2-3 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; cong-app; subst; trans; sym)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Vec using (Vec; _∷_; []; map; foldl)
open import Data.Vec.Properties
open import Data.Nat using (ℕ; suc)
open import Data.Bool using (_∧_; _∨_; not; _xor_)
open import Data.Bool.Properties
open import Function.Base
open import Binary.Base
open import Binary.AddProperties
open import Binary.Comparison.Base
open import Binary.Comparison.Properties
open import Binary.Properties
open import Binary.DozMinMax.Base
open import Binary.DozMinMax.Properties
open import Binary.Absolute.Base
open import Binary.Comparison.Properties
open import Binary.AddProperties
open import Binary.HackersDelight.2-19

-- Prerequisite theorems
sub-le-xor-gt : ∀ {n} {xs ys : Binary (suc n)} → xs >ᵘ ys → (xs - ys) ≤ᵘ (xs ^ ys)
sub-le-xor-gt {ℕ.zero} {O ∷ []} {O ∷ []} _ = inj₂ refl
sub-le-xor-gt {ℕ.zero} {O ∷ []} {I ∷ []} gth = ⊥-elim (gth (inj₁ (lt-head refl lt)))
sub-le-xor-gt {ℕ.zero} {I ∷ []} {O ∷ []} _ = inj₂ refl
sub-le-xor-gt {ℕ.zero} {I ∷ []} {I ∷ []} _ = inj₂ refl
sub-le-xor-gt {suc n} {x ∷ xs} {y ∷ ys} gth with x | y
... | O | O = ≤ᵘ-cons-general' (sub-le-xor-gt (>ᵘ-cons-general gth))
... | O | I rewrite sym (dec-inc-elim (rca xs (~ ys) O)) 
                    | sym (rca-carry-lift-inc xs (~ ys))
                    | rca-carry-transpose-incʳ xs (~ ys) =
  let
    xs>ys = >ᵘ-cons-general gth
    ih = sub-le-xor-gt xs>ys
    dec<self = dec-lt (>ᵘ-to-<ᵘ (sub->ᵘ-zero xs>ys))
  in inj₁ (lt-tail (<ᵘ-≤ᵘ-trans dec<self ih))
... | I | I rewrite rca-carry-transpose-incʳ xs (~ ys) = ≤ᵘ-cons-general' (sub-le-xor-gt (>ᵘ-cons-general gth))
... | I | O with trichotomyᵘ xs ys
...   | tri-lt lth = ⊥-elim (gth (inj₁ (lt-tail lth)))
...   | tri-eq eqh rewrite eqh | +-elimʳ ys | ^-same ys = inj₂ refl
...   | tri-gt gth' = ≤ᵘ-cons-general' (sub-le-xor-gt gth')

inc-absurd : ∀ {n} {xs ys : Binary (suc n)} → xs <ᵘ ys → ys <ᵘ inc xs → ⊥
inc-absurd {ℕ.zero} {O ∷ []} {O ∷ []} (lt-head _ ()) _
inc-absurd {ℕ.zero} {O ∷ []} {I ∷ []} _ (lt-head _ ())
inc-absurd {ℕ.zero} {I ∷ []} {O ∷ []} (lt-head _ ()) _
inc-absurd {ℕ.zero} {I ∷ []} {I ∷ []} (lt-head _ ()) _
inc-absurd {suc n} {O ∷ xs} {O ∷ ys} (lt-tail xs<ys) (lt-tail ys<xs) = <ᵘ-asym xs<ys ys<xs
inc-absurd {suc n} {O ∷ xs} {O ∷ ys} (lt-tail xs<ys) (lt-head refl lt) = <ᵘ-irrefl xs<ys
inc-absurd {suc n} {O ∷ xs} {O ∷ ys} (lt-head refl ()) _
inc-absurd {suc n} {O ∷ xs} {I ∷ ys} (lt-tail xs<ys) (lt-tail ys<xs) = <ᵘ-asym xs<ys ys<xs
inc-absurd {suc n} {O ∷ xs} {I ∷ ys} (lt-tail xs<ys) (lt-head refl ())
inc-absurd {suc n} {O ∷ xs} {I ∷ ys} (lt-head refl lt) (lt-tail ys<xs) = <ᵘ-irrefl ys<xs
inc-absurd {suc n} {O ∷ xs} {I ∷ ys} (lt-head refl lt) (lt-head refl ())
inc-absurd {suc n} {I ∷ xs} {O ∷ ys} (lt-tail xs<ys) (lt-tail ys<inc-xs) = inc-absurd xs<ys ys<inc-xs
inc-absurd {suc n} {I ∷ xs} {O ∷ ys} (lt-tail xs<ys) (lt-head refl ())
inc-absurd {suc n} {I ∷ xs} {O ∷ ys} (lt-head refl ()) _
inc-absurd {suc n} {I ∷ xs} {I ∷ ys} (lt-tail xs<ys) (lt-tail ys<inc-xs) = inc-absurd xs<ys ys<inc-xs
inc-absurd {suc n} {I ∷ xs} {I ∷ ys} (lt-tail xs<ys) (lt-head refl ())
inc-absurd {suc n} {I ∷ xs} {I ∷ ys} (lt-head refl ()) _

abs-sub≡max-sub-min : ∀ {n} (xs ys : Binary (suc n)) → abs-sub xs ys ≡ (maxᵘ xs ys - minᵘ xs ys)
abs-sub≡max-sub-min {n} xs ys rewrite maxᵘ≡+-dozᵘ xs ys 
                                    | minᵘ≡sub-dozᵘ xs ys 
                                    with trichotomyᵘ xs ys
... | tri-lt _ rewrite nneg-zero≡zero {n}
                     | +-identityʳ ys
                     | +-identityʳ xs 
                     = refl
... | tri-eq eqh rewrite eqh
                       | +-elimʳ ys
                       | +-identityʳ ys
                       | nneg-zero≡zero {n}
                       | +-identityʳ ys
                       | +-elimʳ ys
                       = refl
... | tri-gt _ rewrite nneg-distrib xs (- ys)
                     | nneg-involutive ys
                     | +-comm xs (- ys)
                     | sym (+-assoc ys (- ys) xs)
                     | +-elimʳ ys
                     | +-identityˡ xs
                     | sym (+-assoc xs (- xs) ys)
                     | +-elimʳ xs
                     | +-identityˡ ys
                     | +-comm (- ys) xs
                     = refl

-- Actual theorems
^-lte-∥ : ∀ {n} {xs ys : Binary (suc n)} → (xs ^ ys) ≤ᵘ (xs ∥ ys)
^-lte-∥ {ℕ.zero} {x ∷ []} {y ∷ []} with x | y
... | O | O = inj₂ refl
... | I | O = inj₂ refl
... | O | I = inj₂ refl
... | I | I = inj₁ (lt-head refl lt)
^-lte-∥ {suc n} {x ∷ xs} {y ∷ ys} with ^-lte-∥ {n} {xs} {ys} | x | y
... | inj₁ h1 | _ | _ = inj₁ (lt-tail h1)
... | inj₂ eq | O | O = inj₂ (cong (O ∷_) eq)
... | inj₂ eq | I | O = inj₂ (cong (I ∷_) eq)
... | inj₂ eq | O | I = inj₂ (cong (I ∷_) eq)
... | inj₂ eq | I | I = inj₁ (lt-head eq lt)

&-lte-== : ∀ {n} {xs ys : Binary (suc n)} → (xs & ys) ≤ᵘ (xs == ys)
&-lte-== {ℕ.zero} {x ∷ []} {y ∷ []} with x | y
... | O | O = inj₁ (lt-head refl lt)
... | I | O = inj₂ refl
... | O | I = inj₂ refl
... | I | I = inj₂ refl
&-lte-== {suc n} {x ∷ xs} {y ∷ ys} with &-lte-== {n} {xs} {ys} | x | y
... | inj₁ h1 | _ | _ = inj₁ (lt-tail h1)
... | inj₂ eq | O | O = inj₁ (lt-head eq lt)
... | inj₂ eq | I | O = inj₂ (cong (O ∷_) eq)
... | inj₂ eq | O | I = inj₂ (cong (O ∷_) eq)
... | inj₂ eq | I | I = inj₂ (cong (I ∷_) eq)

∥-≥ᵘ-maxᵘ : ∀ {n} (xs ys : Binary (suc n)) → (xs ∥ ys) ≥ᵘ maxᵘ xs ys
∥-≥ᵘ-maxᵘ xs ys with trichotomyᵘ xs ys
... | tri-lt _ = ∥-≥ᵘ-right
... | tri-eq _ = ∥-≥ᵘ-left
... | tri-gt _ = ∥-≥ᵘ-left

&-≤ᵘ-minᵘ : ∀ {n} (xs ys : Binary (suc n)) → (xs & ys) ≤ᵘ minᵘ xs ys
&-≤ᵘ-minᵘ xs ys with trichotomyᵘ xs ys
... | tri-lt _ = &-≤ᵘ-left
... | tri-eq _ = &-≤ᵘ-right
... | tri-gt _ = &-≤ᵘ-right

∥-lte-+ : ∀ {n} {xs ys : Binary (suc n)} → AddNotOverflow xs ys → (xs ∥ ys) ≤ᵘ (xs + ys)
∥-lte-+ {ℕ.zero} {O ∷ []} {O ∷ []} noh = inj₂ refl
∥-lte-+ {ℕ.zero} {I ∷ []} {O ∷ []} noh = inj₂ refl
∥-lte-+ {ℕ.zero} {O ∷ []} {I ∷ []} noh = inj₂ refl
∥-lte-+ {ℕ.zero} {I ∷ []} {I ∷ []} noh with noh
... | (inj₁ (lt-head refl ()))
... | (inj₂ ())
∥-lte-+ {suc n} {O ∷ xs} {O ∷ ys} noh =
  let
    ih = ∥-lte-+ (≤ᵘ-cons-general noh)
  in
    ≤ᵘ-cons-general' ih
∥-lte-+ {suc n} {I ∷ xs} {O ∷ ys} noh = 
  let
    ih = ∥-lte-+ (≤ᵘ-cons-general noh)
  in
    ≤ᵘ-cons-general' ih
∥-lte-+ {suc n} {O ∷ xs} {I ∷ ys} noh = 
  let
    ih = ∥-lte-+ (≤ᵘ-cons-general noh)
  in
    ≤ᵘ-cons-general' ih
∥-lte-+ {suc n} {I ∷ xs} {I ∷ ys} noh =
  let
    ys<~xs = ≤ᵘ-cons-general-strict noh
    ih = ∥-lte-+ (inj₁ ys<~xs)
    inc-lth = +-<ᵘ-inc ys<~xs
    ih' = ≤ᵘ-<ᵘ-trans ih inc-lth
  in
    inj₁ ((lt-tail (subst ((xs ∥ ys) <ᵘ_) (sym (rca-carry-lift-inc xs ys)) ih')))

∥-gt-+ : ∀ {n} {xs ys : Binary (suc n)} → AddOverflow xs ys → (xs ∥ ys) >ᵘ (xs + ys)
∥-gt-+ {ℕ.zero} {O ∷ []} {O ∷ []} oh _ = oh (inj₁ (lt-head refl lt))
∥-gt-+ {ℕ.zero} {I ∷ []} {O ∷ []} oh _ = oh (inj₂ refl)
∥-gt-+ {ℕ.zero} {O ∷ []} {I ∷ []} oh _ = oh (inj₂ refl)
∥-gt-+ {ℕ.zero} {I ∷ []} {I ∷ []} oh h = oh h
∥-gt-+ {suc n} {O ∷ xs} {O ∷ ys} oh h =
  let
    ih = ∥-gt-+ (>ᵘ-cons-general oh)
    hh = ≤ᵘ-cons-general h
  in
    ih hh
∥-gt-+ {suc n} {I ∷ xs} {O ∷ ys} oh h = let
    ih = ∥-gt-+ (>ᵘ-cons-general oh)
    hh = ≤ᵘ-cons-general h
  in
    ih hh
∥-gt-+ {suc n} {O ∷ xs} {I ∷ ys} oh h = let
    ih = ∥-gt-+ (>ᵘ-cons-general oh)
    hh = ≤ᵘ-cons-general h
  in 
    ih hh
∥-gt-+ {suc n} {I ∷ xs} {I ∷ ys} oh h with h
... | (inj₁ (lt-tail lth)) = let
    kh = >ᵘ-cons-general-weak oh
  in
    lemma-contra kh lth
  where
    contra-comp : ys ≡ (~ xs) → (xs ∥ ys) <ᵘ (rca xs ys I) → ⊥
    contra-comp h lth rewrite h 
                      | ∥-inverseʳ xs 
                      | rca-carry-lift-inc xs (~ xs) 
                      | ~-+-ones xs 
                      | inc-ones≡zero {suc n} 
                      = ones-≥ᵘ-zero lth

    contra-ovf : ys >ᵘ (~ xs) → (xs ∥ ys) <ᵘ (rca xs ys I) → ⊥
    contra-ovf h lth rewrite rca-carry-lift-inc xs ys =
      inc-absurd (>ᵘ-to-<ᵘ (∥-gt-+ h)) lth

    lemma-contra : ys ≥ᵘ (~ xs)
                 → (xs ∥ ys) <ᵘ (rca xs ys I)
                 → ⊥
    lemma-contra geh lth with split-≥ᵘ geh
    ... | inj₁ eq = contra-comp eq lth
    ... | inj₂ ovf = contra-ovf ovf lth
... | (inj₁ (lt-head a ()))
... | (inj₂ ())

-- We use abs-sub as it's more trivial to prove without proving the subtraction's overflow
-- properties, since abs-sub guarantees us that the whole process must be evaluated in unsigned
-- realm.
abs-sub-lte-xor : ∀ {n} {xs ys : Binary (suc n)} → abs-sub xs ys ≤ᵘ (xs ^ ys)
abs-sub-lte-xor {n} {xs} {ys} with trichotomyᵘ xs ys
... | tri-lt lth rewrite ^-comm xs ys = sub-le-xor-gt (<ᵘ-to->ᵘ lth)
... | tri-eq eqh rewrite eqh | ^-same ys = inj₂ refl
... | tri-gt gth = sub-le-xor-gt gth

