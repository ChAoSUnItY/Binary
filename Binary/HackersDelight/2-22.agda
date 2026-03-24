module Binary.HackersDelight.2-22 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; cong-app; subst; trans; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Vec using (Vec; _∷_; []; map; zipWith)
open import Data.Vec.Properties
open import Data.Nat using (ℕ; suc)
open import Data.Bool using (_∧_; _∨_; not; _xor_)
open import Data.Bool.Properties
open import Function.Base
open import Binary.Base
open import Binary.Properties
open import Binary.AddProperties

-- FIXME: Can we lift the level up so these function can be more useful?

-- Specific version of shannon expansion
shannon-expansion' : ∀ (x y z : Bit) (f : Bit → Bit → Bit → Bit) → f x y z ≡ ((not z) ∧ f x y O) xor (z ∧ f x y I)
shannon-expansion' x y O f rewrite xor-identityʳ (f x y O) = refl
shannon-expansion' x y I f = refl

decomposition-theorem : ∀ (x y z : Bit) (f : Bit → Bit → Bit → Bit) → f x y z ≡ (f x y O) xor (z ∧ (f x y O xor f x y I))
decomposition-theorem x y z f = begin
    f x y z
  ≡⟨ shannon-expansion' x y z f ⟩
    not z ∧ f x y O xor z ∧ f x y I
  ≡⟨ cong (λ l → l ∧ f x y O xor z ∧ f x y I) (sym (true-xor z)) ⟩
    (I xor z) ∧ f x y O xor z ∧ f x y I
  ≡⟨ cong (λ l → l xor z ∧ f x y I) (∧-distribʳ-xor (f x y O) I z) ⟩
    (f x y O xor z ∧ f x y O) xor z ∧ f x y I
  ≡⟨ xor-assoc (f x y O) (z ∧ f x y O) (z ∧ f x y I) ⟩
    f x y O xor z ∧ f x y O xor z ∧ f x y I
  ≡⟨ cong (f x y O xor_) (sym (∧-distribˡ-xor z (f x y O) (f x y I))) ⟩
    f x y O xor z ∧ (f x y O xor f x y I)
  ∎

-- If there's an instance shows that f ≗ zipWith (λ xs ys zs → zipWith (λ g c → g c) (zipWith f' xs ys) zs)
-- then the later shannon-expansion-ext' would be valid
record Vectorized3 (f' : Bit → Bit → Bit → Bit) (f : ∀ {n} → Binary n → Binary n → Binary n → Binary n) : Set where
  field
    vf-nil  : f [] [] [] ≡ []
    vf-cons : ∀ {n} x y z (xs ys zs : Binary n) → 
             f (x ∷ xs) (y ∷ ys) (z ∷ zs) ≡ f' x y z  ∷ f xs ys zs

instance
  zipWith-vectorized3 : ∀ {f' : Bit → Bit → Bit → Bit} → Vectorized3 f' (λ xs ys zs → zipWith (λ g c → g c) (zipWith f' xs ys) zs)
  zipWith-vectorized3 {f'} = record { vf-nil = refl ; vf-cons = λ _ _ _ _ _ _ → refl }

-- Expands the proof into N-bit binary form
shannon-expansion-ext' : ∀ {n} (xs ys zs : Binary n) (f : ∀ {n'} → Binary n' → Binary n' → Binary n' → Binary n')
  (f' : Bit → Bit → Bit → Bit) {{vectorizable : Vectorized3 f' f}} → f xs ys zs ≡ ((~ zs) & f xs ys (zero n)) ^ (zs & f xs ys (ones n))
shannon-expansion-ext' {ℕ.zero} [] [] [] f _ {{hyp}} rewrite &-identityˡ (f [] [] []) | ^-same (f [] [] []) = Vectorized3.vf-nil hyp
shannon-expansion-ext' {suc n} (x ∷ xs) (y ∷ ys) (z ∷ zs) f f' {{hyp}} = begin
    f (x ∷ xs) (y ∷ ys) (z ∷ zs)
  ≡⟨ (Vectorized3.vf-cons hyp) {n} x y z xs ys zs ⟩
    f' x y z ∷ f xs ys zs
  ≡⟨ cong₂ (_∷_) (shannon-expansion' x y z f') (shannon-expansion-ext' xs ys zs f f' {{hyp}}) ⟩
    (not z ∧ f' x y O xor z ∧ f' x y I) ∷
      ~ zs & f xs ys (zero n) ^ zs & f xs ys (ones n)
  ≡⟨ zipWith-cons (not z ∧ f' x y O) (z ∧ f' x y I) (~ zs & f xs ys (zero n)) (zs & f xs ys (ones n)) (_xor_) ⟩
    (not z ∧ f' x y O ∷ ~ zs & f xs ys (zero n)) ^
      (z ∧ f' x y I ∷ zs & f xs ys (ones n))
  ≡⟨ cong₂ (_^_)
     (zipWith-cons (not z) (f' x y O) (~ zs) (f xs ys (zero n)) (_∧_))
     (zipWith-cons z (f' x y I) zs (f xs ys (ones n)) (_∧_)) ⟩
    (~ (z ∷ zs)) & (f' x y O ∷ f xs ys (zero n)) ^
      (z ∷ zs) & (f' x y I ∷ f xs ys (ones n))
  ≡⟨ cong₂ (_^_)
     (cong (~ (z ∷ zs) &_) (sym ((Vectorized3.vf-cons hyp) {n} x y O xs ys (zero n))))
     (cong ((z ∷ zs) &_) (sym ((Vectorized3.vf-cons hyp) {n} x y I xs ys (ones n)))) ⟩
    ~ (z ∷ zs) & f (x ∷ xs) (y ∷ ys) (zero (suc n)) ^
      (z ∷ zs) & f (x ∷ xs) (y ∷ ys) (ones (suc n))
  ∎

decomposition-theorem-ext : ∀ {n} (xs ys zs : Binary n) (f : ∀ {n'} → Binary n' → Binary n' → Binary n' → Binary n')
  (f' : Bit → Bit → Bit → Bit) {{vectorizable : Vectorized3 f' f}} → f xs ys zs ≡ (f xs ys (zero n)) ^ (zs & (f xs ys (zero n) ^ f xs ys (ones n)))
decomposition-theorem-ext {n} xs ys zs f f' {{hyp}} = begin
    f xs ys zs
  ≡⟨ shannon-expansion-ext' xs ys zs f f' {{hyp}} ⟩
    ~ zs & f xs ys (zero n) ^ zs & f xs ys (ones n)
  ≡⟨ cong (λ l → l & f xs ys (zero n) ^ zs & f xs ys (ones n)) (sym (ones-^ zs)) ⟩
    (ones n ^ zs) & f xs ys (zero n) ^ zs & f xs ys (ones n)
  ≡⟨ cong (λ l → l ^ zs & f xs ys (ones n)) (&-distrib-^ʳ (f xs ys (zero n)) (ones n) zs) ⟩
    ones n & f xs ys (zero n) ^ zs & f xs ys (zero n) ^
      zs & f xs ys (ones n)
  ≡⟨ ^-assoc (ones n & f xs ys (zero n)) (zs & f xs ys (zero n)) (zs & f xs ys (ones n)) ⟩
    ones n & f xs ys (zero n) ^
      (zs & f xs ys (zero n) ^ zs & f xs ys (ones n))
  ≡⟨ cong (λ l → l ^ (zs & f xs ys (zero n) ^ zs & f xs ys (ones n))) (&-identityˡ (f xs ys (zero n))) ⟩
    f xs ys (zero n) ^ (zs & f xs ys (zero n) ^ zs & f xs ys (ones n))
  ≡⟨ cong (f xs ys (zero n) ^_) (sym (&-distrib-^ˡ zs (f xs ys (zero n)) (f xs ys (ones n)))) ⟩
    f xs ys (zero n) ^ zs & (f xs ys (zero n) ^ f xs ys (ones n))
  ∎

-- Example: f(x, y, z) = xy¬z + x¬yz + ¬xyz
private
  example-func' : (xs ys zs : Bit) → Bit
  example-func' x y z = (x ∧ y ∧ not z) ∨ (x ∧ not y ∧ z) ∨ (not x ∧ y ∧ z)

  example-func : ∀ {n} (xs ys zs : Binary n) → Binary n
  example-func xs ys zs = zipWith (λ g c → g c) (zipWith example-func' xs ys) zs

  -- Lemma for the False case
  example-false : ∀ {n} (xs ys : Binary n) → 
    example-func xs ys (zero n) ≡ xs & ys
  example-false [] [] = refl
  example-false {suc n} (x ∷ xs) (y ∷ ys) = begin
      example-func (x ∷ xs) (y ∷ ys) (zero (suc n))
    ≡⟨⟩
      example-func' x y O ∷ zipWith (λ g → g) (zipWith example-func' xs ys) (zero n)
    ≡⟨ cong (example-func' x y O ∷_) (example-false xs ys) ⟩
      (x ∧ y ∧ I ∨ x ∧ not y ∧ O ∨ not x ∧ y ∧ O) ∷ xs & ys
    ≡⟨ cong₂ (λ l r → (x ∧ y ∧ I ∨ l ∨ r) ∷ xs & ys) 
       (trans (sym (∧-assoc x (not y) O)) (∧-zeroʳ (x ∧ not y)))
       (trans (sym (∧-assoc (not x) y O)) (∧-zeroʳ (not x ∧ y))) ⟩
      (x ∧ y ∧ I ∨ O ∨ O) ∷ xs & ys
    ≡⟨ cong (λ l → l ∷ xs & ys) (trans (∨-identityʳ (x ∧ y ∧ I)) (trans (sym (∧-assoc x y I)) (∧-identityʳ (x ∧ y)))) ⟩
      x ∧ y ∷ xs & ys
    ≡⟨⟩
      (x ∷ xs) & (y ∷ ys)
    ∎

  -- Lemma for the True case
  example-true : ∀ {n} (xs ys : Binary n) → 
    example-func xs ys (ones n) ≡ xs & ~ ys ∥ ~ xs & ys
  example-true [] [] = refl
  example-true {suc n} (x ∷ xs) (y ∷ ys) = begin
      example-func (x ∷ xs) (y ∷ ys) (ones (suc n))
    ≡⟨⟩
      example-func' x y I ∷ zipWith (λ g → g) (zipWith example-func' xs ys) (ones n)
    ≡⟨ cong (example-func' x y I ∷_) (example-true xs ys) ⟩
      (x ∧ y ∧ O ∨ x ∧ not y ∧ I ∨ not x ∧ y ∧ I) ∷ xs & ~ ys ∥ ~ xs & ys
    ≡⟨ cong (λ l → (l ∨ x ∧ not y ∧ I ∨ not x ∧ y ∧ I) ∷ xs & ~ ys ∥ ~ xs & ys) (trans (sym (∧-assoc x y O)) (∧-zeroʳ (x ∧ y))) ⟩
      (x ∧ not y ∧ I ∨ not x ∧ y ∧ I) ∷ xs & ~ ys ∥ ~ xs & ys
    ≡⟨ cong₂ (λ l r → (l ∨ r) ∷ xs & ~ ys ∥ ~ xs & ys)
       (trans (sym (∧-assoc x (not y) I)) (∧-identityʳ (x ∧ not y)))
       (trans (sym (∧-assoc (not x) y I)) (∧-identityʳ (not x ∧ y))) ⟩
      (x ∧ not y ∨ not x ∧ y) ∷ xs & ~ ys ∥ ~ xs & ys
    ≡⟨ zipWith-cons (x ∧ not y) (not x ∧ y) (xs & ~ ys) (~ xs & ys) _∨_ ⟩
      (x ∧ not y ∷ xs & ~ ys) ∥ (not x ∧ y ∷ ~ xs & ys)
    ≡⟨ cong₂ (_∥_)
       (zipWith-cons x (not y) xs (~ ys) _∧_)
       (zipWith-cons (not x) y (~ xs) ys _∧_) ⟩
      (x ∷ xs) & ~ (y ∷ ys) ∥ ~ (x ∷ xs) & (y ∷ ys)
    ∎

  example : ∀ {n} (xs ys zs : Binary n) → example-func xs ys zs ≡ xs & ys ^ zs & (xs ∥ ys)
  example {n} xs ys zs = begin
      example-func xs ys zs
    ≡⟨ decomposition-theorem-ext xs ys zs example-func example-func' ⟩
      example-func xs ys (zero n) ^
        zs & (example-func xs ys (zero n) ^ example-func xs ys (ones n))
    ≡⟨ cong₂ (λ l r → l ^ zs & (l ^ r)) (example-false xs ys) (example-true xs ys) ⟩
      xs & ys ^ zs & (xs & ys ^ (xs & ~ ys ∥ ~ xs & ys))
    ≡⟨ cong (λ l → xs & ys ^ zs & l) (hyp xs ys) ⟩
      xs & ys ^ zs & (xs ∥ ys)
    ∎
    where
      hyp : ∀ {n} (xs ys : Binary n) → xs & ys ^ (xs & ~ ys ∥ ~ xs & ys) ≡ xs ∥ ys
      hyp [] [] = refl
      hyp {suc n} (O ∷ xs) (y ∷ ys) = cong (y ∷_) (hyp xs ys)
      hyp {suc n} (I ∷ xs) (y ∷ ys) rewrite ∨-identityʳ (not y)
                                          | sym (not-distribʳ-xor y y)
                                          | xor-same y = cong (I ∷_) (hyp xs ys)

-- COROLLARY: If a computer's instruction set includes an instruction for each of the 16 Boolean functions of 2 variables, 
--            then any boolean function of 3 variables can be implemented with 4 (or fewer) instructions.
