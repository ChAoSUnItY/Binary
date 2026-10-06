module Binary.AddProperties where

open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Vec using (Vec; _∷_; _∷ʳ_; []; _++_; replicate; map; zip; zipWith)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂; map₁)
open import Data.Nat using (ℕ; suc)
open import Data.Bool using (_∧_; _∨_; not; _xor_; if_then_else_)
open import Data.Bool.Properties
open import Function
open import Tactic.Cong
open import Binary.Base
open import Binary.Properties

-- Basic RCA theorems
rca-no-carry : ∀ {n} (x y : Bit) (xs ys : Binary n) → rca (x ∷ xs) (y ∷ ys) O ≡ (x xor y) ∷ rca xs ys (x ∧ y)
rca-no-carry {n} x y xs ys = begin
    rca (x ∷ xs) (y ∷ ys) O
  ≡⟨⟩
    ((x xor y) xor O) ∷ rca xs ys (x ∧ y ∨ O ∧ (x xor y))
  ≡⟨ cong (_∷ rca xs ys (x ∧ y ∨ O ∧ (x xor y))) (xor-identityʳ (x xor y)) ⟩
    (x xor y) ∷ rca xs ys (x ∧ y ∨ O ∧ (x xor y))
  ≡⟨ cong! (∧-zeroˡ (x xor y)) ⟩
    (x xor y) ∷ rca xs ys (x ∧ y ∨ O)
  ≡⟨ cong! (∨-identityʳ (x ∧ y)) ⟩
    (x xor y) ∷ rca xs ys (x ∧ y)
  ≡⟨⟩
    (x xor y) ∷ rca xs ys (x ∧ y)
  ∎

sum : Bit → Bit → Bit → Bit
sum x y c = (x xor y) xor c

carry : Bit → Bit → Bit → Bit
carry x y c = (x ∧ y) ∨ (c ∧ (x xor y))

-- Add result gives 3 possible addition outcomes for theorems to prove with,
-- without the need to prove an additional unnecessary clause for 
-- "either a bit is true".
data AddResult (x y : Bit) : Set where
  case-zero  : (x ≡ O) → (y ≡ O) → AddResult x y
  case-one   : (x ∧ y ≡ O) → (x ∨ y ≡ I) → (x xor y ≡ I) → AddResult x y
  case-carry : (x ≡ I) → (y ≡ I) → AddResult x y

add-result : ∀ (x y : Bit) → AddResult x y
add-result O O = case-zero  refl refl
add-result O I = case-one   refl refl refl
add-result I O = case-one   refl refl refl
add-result I I = case-carry refl refl

-- Advanced RCA theorems
rca-comm : ∀ {n} (xs ys : Binary n) (c : Bit) → rca xs ys c ≡ rca ys xs c
rca-comm [] [] _ = refl
rca-comm (x ∷ xs) (y ∷ ys) c = begin
    rca (x ∷ xs) (y ∷ ys) c
  ≡⟨⟩
    ((x xor y) xor c) ∷ rca xs ys (x ∧ y ∨ c ∧ (x xor y))
  ≡⟨ cong (λ l → (l xor c) ∷ rca xs ys (x ∧ y ∨ c ∧ l)) (xor-comm x y) ⟩
    ((y xor x) xor c) ∷ rca xs ys (x ∧ y ∨ c ∧ (y xor x))
  ≡⟨ cong (λ l → ((y xor x) xor c) ∷ rca xs ys (l ∨ c ∧ (y xor x))) (∧-comm x y) ⟩
    ((y xor x) xor c) ∷ rca xs ys (y ∧ x ∨ c ∧ (y xor x))
  ≡⟨ cong (((y xor x) xor c) ∷_) (rca-comm xs ys (y ∧ x ∨ c ∧ (y xor x))) ⟩
    ((y xor x) xor c) ∷ rca ys xs (y ∧ x ∨ c ∧ (y xor x))
  ≡⟨⟩
    rca (y ∷ ys) (x ∷ xs) c
  ∎

rca-carry-transpose-incˡ : ∀ {n} (xs ys : Binary n) → rca xs ys I ≡ rca (inc xs) ys O
rca-carry-transpose-incˡ [] [] = refl
rca-carry-transpose-incˡ (O ∷ xs) (y ∷ ys) with y
... | O = refl
... | I = refl
rca-carry-transpose-incˡ (I ∷ xs) (O ∷ ys) = begin
    rca (I ∷ xs) (O ∷ ys) I
  ≡⟨⟩
    O ∷ rca xs ys I
  ≡⟨ cong (O ∷_) (rca-carry-transpose-incˡ xs ys) ⟩
    rca (inc (I ∷ xs)) (O ∷ ys) O
  ∎
rca-carry-transpose-incˡ (I ∷ xs) (I ∷ ys) = begin
    rca (I ∷ xs) (I ∷ ys) I
  ≡⟨⟩
    I ∷ rca xs ys I
  ≡⟨ cong (I ∷_) (rca-carry-transpose-incˡ xs ys) ⟩
    rca (inc (I ∷ xs)) (I ∷ ys) O
  ∎

rca-carry-transpose-incʳ : ∀ {n} (xs ys : Binary n) → rca xs ys I ≡ rca xs (inc ys) O
rca-carry-transpose-incʳ xs ys = begin
    rca xs ys I
  ≡⟨ rca-comm xs ys I ⟩
    rca ys xs I
  ≡⟨ rca-carry-transpose-incˡ ys xs ⟩
    rca (inc ys) xs O
  ≡⟨ rca-comm (inc ys) xs O ⟩
    rca xs (inc ys) O
  ∎

rca-carry-lift-inc : ∀ {n} (xs ys : Binary n) → rca xs ys I ≡ inc (rca xs ys O)
rca-carry-lift-inc [] [] = refl
rca-carry-lift-inc (x ∷ xs) (y ∷ ys) with add-result x y
... | case-zero refl refl = refl
... | case-carry refl refl = refl
... | case-one h∧ _ h⊕ rewrite h⊕ | h∧ = cong (O ∷_) (rca-carry-lift-inc xs ys)

rca-inc-liftˡ : ∀ {n} (xs ys : Binary n) (c : Bit) → rca (inc xs) ys c ≡ inc (rca xs ys c)
rca-inc-liftˡ xs ys O = begin
    rca (inc xs) ys O
  ≡⟨ sym (rca-carry-transpose-incˡ xs ys) ⟩
    rca xs ys I
  ≡⟨ rca-carry-lift-inc xs ys ⟩
    inc (rca xs ys O)
  ∎
rca-inc-liftˡ xs ys I = begin
    rca (inc xs) ys I
  ≡⟨ rca-carry-lift-inc (inc xs) ys ⟩
    inc (rca (inc xs) ys O)
  ≡⟨ cong (inc) (sym (rca-carry-transpose-incˡ xs ys)) ⟩
    inc (rca xs ys I)
  ∎

rca-inc-liftʳ : ∀ {n} (xs ys : Binary n) (c : Bit) → rca xs (inc ys) c ≡ inc (rca xs ys c)
rca-inc-liftʳ xs ys c = begin
    rca xs (inc ys) c
  ≡⟨ rca-comm xs (inc ys) c ⟩
    rca (inc ys) xs c
  ≡⟨ rca-inc-liftˡ ys xs c ⟩
    inc (rca ys xs c)
  ≡⟨ cong (inc) (rca-comm ys xs c) ⟩
    inc (rca xs ys c)
  ∎

-- Conditional increment variants,
-- this is usually used to push uncomputed bits
-- with inc, which is not possible with original `inc`

inc? : ∀ {n} → Bit → Binary n → Binary n
inc? c xs = if c then inc xs else xs

inc?-liftˡ : ∀ {n} b (xs ys : Binary n) → inc? b xs + ys ≡ inc? b (xs + ys)
inc?-liftˡ O xs ys = refl
inc?-liftˡ I xs ys = rca-inc-liftˡ xs ys O

inc?-liftʳ : ∀ {n} b (xs ys : Binary n) → xs + inc? b ys ≡ inc? b (xs + ys)
inc?-liftʳ O xs ys = refl
inc?-liftʳ I xs ys = rca-inc-liftʳ xs ys O

inc?-lift : ∀ {n} b (xs ys : Binary n) → 
  rca xs ys b ≡ inc? b (xs + ys)
inc?-lift b xs ys with b
... | O = refl
... | I rewrite rca-carry-lift-inc xs ys = refl

rca-cons-inc? : ∀ {n} (xs ys : Binary n) (x y c : Bit) →
  rca (x ∷ xs) (y ∷ ys) c ≡ sum x y c ∷ inc? (carry x y c) (xs + ys)
rca-cons-inc? xs ys x y c = cong (sum x y c ∷_) (inc?-lift (carry x y c) xs ys)

rca-inc-comm : ∀ {n} (xs ys : Binary n) (c : Bit) → rca (inc xs) ys c ≡ rca xs (inc ys) c
rca-inc-comm xs ys c = begin
    rca (inc xs) ys c
  ≡⟨ rca-inc-liftˡ xs ys c ⟩
    inc (rca xs ys c)
  ≡⟨ sym (rca-inc-liftʳ xs ys c) ⟩
    rca xs (inc ys) c
  ∎

rca-carry-commˡ : ∀ {n} (xs ys zs : Binary n) (c c' : Bit) → rca (rca xs ys c) zs c' ≡ rca (rca xs ys c') zs c
rca-carry-commˡ xs ys zs c c' with c | c'
... | O | O = refl
... | I | O = begin
    rca (rca xs ys I) zs O
  ≡⟨ cong (λ l → rca l zs O) (rca-carry-lift-inc xs ys) ⟩
    rca (inc (rca xs ys O)) zs O
  ≡⟨ sym (rca-carry-transpose-incˡ (rca xs ys O) zs) ⟩
    rca (rca xs ys O) zs I
  ∎
... | O | I = begin
    rca (rca xs ys O) zs I
  ≡⟨ rca-carry-transpose-incˡ (rca xs ys O) zs ⟩
    rca (inc (rca xs ys O)) zs O
  ≡⟨ cong (λ l → rca l zs O) (sym (rca-carry-lift-inc xs ys)) ⟩
    rca (rca xs ys I) zs O
  ∎
... | I | I = refl

rca-carry-commʳ : ∀ {n} (xs ys zs : Binary n) (c c' : Bit) → rca xs (rca ys zs c) c' ≡ rca xs (rca ys zs c') c
rca-carry-commʳ xs ys zs c c' = begin
    rca xs (rca ys zs c) c'
  ≡⟨ rca-comm xs (rca ys zs c) c' ⟩
    rca (rca ys zs c) xs c'
  ≡⟨ rca-carry-commˡ ys zs xs c c' ⟩
    rca (rca ys zs c') xs c
  ≡⟨ rca-comm (rca ys zs c') xs c ⟩
    rca xs (rca ys zs c') c
  ∎

-- Associativity

-- Reorganizes bits to correct position in assoc proof
bit-assoc-no-carry : ∀ {n} (x y z : Bit) (t : Binary n) →
  sum (sum x y O) z O ∷ inc? (carry (sum x y O) z O) (inc? (carry x y O) t) ≡
    sum x (sum y z O) O ∷ inc? (carry x (sum y z O) O) (inc? (carry y z O) t)
bit-assoc-no-carry x y z t with x | y | z
... | O | O | O = refl
... | I | O | O = refl
... | O | I | O = refl
... | I | I | O = refl
... | O | O | I = refl
... | I | O | I = refl
... | O | I | I = refl
... | I | I | I = refl

rca-assoc-no-carry : ∀ {n} (xs ys zs : Binary n) → rca (rca xs ys O) zs O ≡ rca xs (rca ys zs O) O
rca-assoc-no-carry [] [] [] = refl
rca-assoc-no-carry (x ∷ xs) (y ∷ ys) (z ∷ zs) = begin
    (x ∷ xs) + (y ∷ ys) + (z ∷ zs)
  ≡⟨ cong (λ l → l + (z ∷ zs)) (rca-cons-inc? xs ys x y O) ⟩
    (sum x y O ∷ inc? (carry x y O) (xs + ys)) + (z ∷ zs)
  ≡⟨ rca-cons-inc? _ zs (sum x y O) z O ⟩
    sum (sum x y O) z O ∷ inc? (carry (sum x y O) z O) (inc? (carry x y O) (xs + ys) + zs)
  ≡⟨ cong (λ l → sum (sum x y O) z O ∷ inc? (carry (sum x y O) z O) l)
      (inc?-liftˡ (carry x y O) (xs + ys) zs) ⟩
    sum (sum x y O) z O ∷ inc? (carry (sum x y O) z O) (inc? (carry x y O) (xs + ys + zs))
  ≡⟨ cong (λ l → sum (sum x y O) z O ∷ inc? (carry (sum x y O) z O) (inc? (carry x y O) l))
      (rca-assoc-no-carry xs ys zs) ⟩
    sum (sum x y O) z O ∷ inc? (carry (sum x y O) z O) (inc? (carry x y O) (xs + (ys + zs)))
  ≡⟨ bit-assoc-no-carry x y z (xs + (ys + zs)) ⟩
    sum x (sum y z O) O ∷ inc? (carry x (sum y z O) O) (inc? (carry y z O) (xs + (ys + zs)))
  ≡⟨ cong (λ l → sum x (sum y z O) O ∷ inc? (carry x (sum y z O) O) l) 
      (sym (inc?-liftʳ (carry y z O) xs (ys + zs))) ⟩
    sum x (sum y z O) O ∷ inc? (carry x (sum y z O) O) (xs + inc? (carry y z O) (ys + zs))
  ≡⟨ sym (rca-cons-inc? xs _ x (sum y z O) O) ⟩
    (x ∷ xs) + (sum y z O ∷ inc? (carry y z O) (ys + zs))
  ≡⟨ cong ((x ∷ xs) +_) (sym (rca-cons-inc? ys zs y z O)) ⟩
    (x ∷ xs) + ((y ∷ ys) + (z ∷ zs))
  ∎

rca-assoc : ∀ {n} (xs ys zs : Binary n) (c c' : Bit) → rca (rca xs ys c) zs c' ≡ rca xs (rca ys zs c) c'
rca-assoc xs ys zs c c' = begin
    rca (rca xs ys c) zs c'
  ≡⟨ inc?-lift c' _ zs ⟩
    inc? c' (rca xs ys c + zs)
  ≡⟨ cong (λ l → inc? c' (l + zs)) (inc?-lift c _ ys ) ⟩
    inc? c' (inc? c (xs + ys) + zs)
  ≡⟨ cong (inc? c') (inc?-liftˡ c (xs + ys) zs) ⟩
    inc? c' (inc? c (xs + ys + zs))
  ≡⟨ cong (λ l → inc? c' (inc? c l)) (rca-assoc-no-carry xs ys zs) ⟩
    inc? c' (inc? c (xs + (ys + zs)))
  ≡⟨ cong (inc? c') (sym (inc?-liftʳ c xs _)) ⟩
    inc? c' (xs + inc? c (ys + zs))
  ≡⟨ cong (λ l → inc? c' (xs + l)) (sym (inc?-lift c ys zs)) ⟩
    inc? c' (xs + rca ys zs c)
  ≡⟨ sym (inc?-lift c' xs _) ⟩
    rca xs (rca ys zs c) c'
  ∎

-- Actual addition theorems to be used with
+-comm : ∀ {n} (xs ys : Binary n) → xs + ys ≡ ys + xs
+-comm xs ys = rca-comm xs ys O

+-identityˡ : ∀ {n} (xs : Binary n) → zero n + xs ≡ xs
+-identityˡ {_}     [] = refl
+-identityˡ {suc n} (x ∷ xs) = begin
    zero (suc n) + (x ∷ xs)
  ≡⟨⟩
    ((O xor x) xor O) ∷ (zero n + xs)
  ≡⟨ cong (_∷ (zero n + xs)) (xor-identityʳ x) ⟩
    x ∷ (zero n + xs)
  ≡⟨ cong (x ∷_) (+-identityˡ xs) ⟩
    x ∷ xs
  ∎

+-identityʳ : ∀ {n} (xs : Binary n) → xs + zero n ≡ xs
+-identityʳ {n} xs = begin
    xs + zero n
  ≡⟨ +-comm xs (zero n) ⟩
    zero n + xs
  ≡⟨ +-identityˡ xs ⟩
    xs
  ∎

+-elimˡ : ∀ {n} (xs : Binary n) → (- xs) + xs ≡ zero n
+-elimˡ {_}     [] = refl
+-elimˡ {suc n} (x ∷ xs) with x
... | O = begin
    (- (O ∷ xs)) + (O ∷ xs)
  ≡⟨⟩
    O ∷ ((- xs) + xs)
  ≡⟨ cong (O ∷_) (+-elimˡ xs) ⟩
    zero (suc n)
  ∎
... | I = begin
    (- (I ∷ xs)) + (I ∷ xs)
  ≡⟨⟩
    O ∷ rca (map not xs) xs I
  ≡⟨ cong (O ∷_) (rca-carry-transpose-incˡ (map not xs) xs) ⟩
    O ∷ ((- xs) + xs)
  ≡⟨ cong (O ∷_) (+-elimˡ xs) ⟩
    zero (suc n)
  ∎

+-elimʳ : ∀ {n} (xs : Binary n) → xs + (- xs) ≡ zero n
+-elimʳ {n} xs = begin
    xs + (- xs)
  ≡⟨ +-comm xs (- xs) ⟩
    (- xs) + xs
  ≡⟨ +-elimˡ xs ⟩
    zero n
  ∎

+-assoc : ∀ {n} (xs ys zs : Binary n) → (xs + ys) + zs ≡ xs + (ys + zs)
+-assoc = rca-assoc-no-carry

-- Algebra properties
module Algebra {n} where
  open import Level using (0ℓ)
  open import Algebra.Bundles
    using (Magma; Semigroup; CommutativeSemigroup; CommutativeMonoid; Monoid)
  open import Algebra.Structures {A = Binary n} _≡_

  -- Structures
  +-isMagma : IsMagma _+_
  +-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        = cong₂ _+_
    }

  +-isSemigroup : IsSemigroup _+_
  +-isSemigroup = record
    { isMagma = +-isMagma
    ; assoc   = +-assoc
    }

  +-isCommutativeSemigroup : IsCommutativeSemigroup _+_
  +-isCommutativeSemigroup = record
    { isSemigroup = +-isSemigroup
    ; comm        = +-comm
    }

  +-0-isMonoid : IsMonoid _+_ (zero n)
  +-0-isMonoid = record
    { isSemigroup = +-isSemigroup
    ; identity    = +-identityˡ , +-identityʳ
    }

  +-0-isCommutativeMonoid : IsCommutativeMonoid _+_ (zero n)
  +-0-isCommutativeMonoid = record
    { isMonoid = +-0-isMonoid
    ; comm     = +-comm
    }
  
  -- Bundles
  +-magma : Magma 0ℓ 0ℓ
  +-magma = record
    { isMagma = +-isMagma
    }

  +-semigroup : Semigroup 0ℓ 0ℓ
  +-semigroup = record
    { isSemigroup = +-isSemigroup
    }

  +-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
  +-commutativeSemigroup = record
    { isCommutativeSemigroup = +-isCommutativeSemigroup
    }

  +-monoid : Monoid 0ℓ 0ℓ
  +-monoid = record
    { isMonoid = +-0-isMonoid
    }

  +-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
  +-commutativeMonoid = record
    { isCommutativeMonoid = +-0-isCommutativeMonoid
    }

-- Additional theorems for rca
~-+-ones : ∀ {n} (xs : Binary n) → xs + (~ xs) ≡ ones n
~-+-ones [] = refl
~-+-ones (x ∷ xs) with x
... | O rewrite ~-+-ones xs = refl
... | I rewrite ~-+-ones xs = refl

~≡ones-sub : ∀ {n} (xs : Binary n) → ~ xs ≡ (ones n) - xs
~≡ones-sub [] = refl
~≡ones-sub {suc n} (x ∷ xs) with x
... | O rewrite cong (I ∷_) (~≡ones-sub xs) = refl
... | I rewrite cong (O ∷_) (~≡ones-sub xs) | rca-carry-transpose-incʳ (ones n) (~ xs) = refl

+-ones≡dec : ∀ {n} (xs : Binary n) → xs + ones n ≡ dec xs
+-ones≡dec [] = refl
+-ones≡dec {suc n} (x ∷ xs) with x
... | O rewrite +-ones≡dec xs = refl
... | I rewrite rca-carry-transpose-incʳ xs (ones n)
              | inc-ones≡zero {n}
              | +-identityʳ xs = refl

nneg-distrib : ∀ {n} (xs ys : Binary n) → - (xs + ys) ≡ (- xs) + (- ys)
nneg-distrib [] [] = refl
nneg-distrib (O ∷ xs) (O ∷ ys) = cong (O ∷_) (nneg-distrib xs ys)
nneg-distrib (O ∷ xs) (I ∷ ys) = cong (I ∷_) (inc-inj (begin
                                   inc (map not (rca xs ys O))
                                 ≡⟨ nneg-distrib xs ys ⟩
                                   (- xs) + (- ys)
                                 ≡⟨ rca-inc-liftʳ (- xs) (~ ys) O ⟩
                                   inc (rca (inc (map not xs)) (map not ys) O)
                                 ∎))
nneg-distrib (I ∷ xs) (O ∷ ys) = cong (I ∷_) (inc-inj (begin
                                  inc (map not (rca xs ys O))
                                 ≡⟨ nneg-distrib xs ys ⟩
                                   (- xs) + (- ys)
                                 ≡⟨ rca-inc-liftˡ (~ xs) (- ys) O ⟩
                                   inc (rca (map not xs) (inc (map not ys)) O)
                                 ∎))
nneg-distrib (I ∷ xs) (I ∷ ys) rewrite rca-carry-transpose-incˡ xs ys
                                     | rca-carry-transpose-incˡ (~ xs) (~ ys)
                                     = cong (O ∷_) (inc-inj (begin
                                         inc (inc (~ (rca (inc xs) ys O)))
                                       ≡⟨ cong (λ l → inc (inc (~ l))) (trans (sym (rca-carry-transpose-incˡ xs ys)) (rca-carry-lift-inc xs ys)) ⟩
                                         inc (inc (~ (inc (rca xs ys O))))
                                       ≡⟨ cong (inc ∘ inc) (~-inc≡dec-~ (rca xs ys O)) ⟩
                                         inc (inc (dec (~ (rca xs ys O))))
                                       ≡⟨ cong inc (inc-dec-elim (~ (rca xs ys O))) ⟩
                                         inc (~ (rca xs ys O))
                                       ≡⟨⟩
                                         - (xs + ys)
                                       ≡⟨ nneg-distrib xs ys ⟩
                                         (- xs) + (- ys)
                                       ≡⟨ rca-inc-liftʳ (- xs) (~ ys) O ⟩
                                         inc (rca (- xs) (~ ys) O)
                                       ∎))
                                       where
                                         -- This proof is also proved in Hacker's Delight, chapter 2-1
                                         ~-inc≡dec-~ : ∀ {n} (zs : Binary n) → ~ (inc zs) ≡ dec (~ zs)
                                         ~-inc≡dec-~ [] = refl
                                         ~-inc≡dec-~ (O ∷ zs) = refl
                                         ~-inc≡dec-~ (I ∷ zs) = cong (I ∷_) (~-inc≡dec-~ zs)
