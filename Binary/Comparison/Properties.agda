module Binary.Comparison.Properties where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; cong-app; subst; trans; sym)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; _∷_; [])
open import Binary.Base
open import Binary.Comparison.Base
open import Binary.Properties
open import Binary.AddProperties

-- Basic properties
-- lt
<ᵘ-irrefl : ∀ {n} {xs : Binary (suc n)} → xs <ᵘ xs → ⊥
<ᵘ-irrefl {suc n} (lt-tail h) = <ᵘ-irrefl h
<ᵘ-irrefl {suc n} (lt-head refl ())

<ᵘ-asym : ∀ {n} {xs ys : Binary (suc n)} → xs <ᵘ ys → ys <ᵘ xs → ⊥
<ᵘ-asym {suc n} (lt-tail h1) (lt-tail h2) = <ᵘ-asym h1 h2
<ᵘ-asym {suc n} (lt-tail h1) (lt-head refl _) = <ᵘ-irrefl h1
<ᵘ-asym {suc n} (lt-head refl _) (lt-tail h2) = <ᵘ-irrefl h2
<ᵘ-asym {suc n} (lt-head _ lt) (lt-head _ ())

<ᵘ-trans : ∀ {n} {xs ys zs : Binary (suc n)} → xs <ᵘ ys → ys <ᵘ zs → xs <ᵘ zs
<ᵘ-trans {suc n} (lt-tail x<y) (lt-tail y<z) = lt-tail (<ᵘ-trans x<y y<z)
<ᵘ-trans {suc n} (lt-tail x<y) (lt-head refl _) = lt-tail x<y
<ᵘ-trans {suc n} (lt-head refl _) (lt-tail y<z) = lt-tail y<z
<ᵘ-trans {suc n} (lt-head _ lt) (lt-head _ ())

<ᵘ-cons-general : ∀ {n} {x y : Bit} {xs ys : Binary (suc n)} 
                {{_ : y ≤bᵘ x}}
                → (x ∷ xs) <ᵘ (y ∷ ys) 
                → xs <ᵘ ys
<ᵘ-cons-general {{_}} (lt-tail h) = h
<ᵘ-cons-general {{inj₁ ()}} (lt-head refl lt)
<ᵘ-cons-general {{inj₂ ()}} (lt-head refl lt)

<ᵘ-cons-general-weak : ∀ {n} {x y : Bit} {xs ys : Binary (suc n)} 
                        → (x ∷ xs) <ᵘ (y ∷ ys) 
                        → xs ≤ᵘ ys
<ᵘ-cons-general-weak (lt-tail lth) = inj₁ lth
<ᵘ-cons-general-weak (lt-head refl lt) = inj₂ refl

-- trichotomy
data Trichotomyᵘ {n} (xs ys : Binary (suc n)) : Set where
  tri-lt : xs <ᵘ ys → Trichotomyᵘ xs ys
  tri-eq : xs ≡ ys → Trichotomyᵘ xs ys
  tri-gt : xs >ᵘ ys → Trichotomyᵘ xs ys

trichotomyᵘ : ∀ {n} (xs ys : Binary (suc n)) → Trichotomyᵘ xs ys
trichotomyᵘ {ℕ.zero} (x ∷ []) (y ∷ []) with x | y
... | O | O = tri-eq refl
... | O | I = tri-lt (lt-head refl lt)
... | I | O = tri-gt (λ { (inj₁ (lt-head refl ()))
                        ; (inj₂ ()) })
... | I | I = tri-eq refl
trichotomyᵘ {suc n} (x ∷ xs) (y ∷ ys) with trichotomyᵘ xs ys
... | tri-lt lth = tri-lt (lt-tail lth)
... | tri-gt gth = tri-gt (λ { (inj₁ (lt-tail l)) → gth (inj₁ l)
                             ; (inj₁ (lt-head refl _)) → gth (inj₂ refl)
                             ; (inj₂ refl) → gth (inj₂ refl) })
... | tri-eq refl with x | y
...   | O | O = tri-eq refl
...   | I | O = tri-gt (λ { (inj₁ (lt-tail l)) → <ᵘ-irrefl l
                          ; (inj₁ (lt-head refl ()))
                          ; (inj₂ ()) })
...   | O | I = tri-lt (lt-head refl lt)
...   | I | I = tri-eq refl

-- lte
≤ᵘ-refl : ∀ {n} {xs : Binary (suc n)} → xs ≤ᵘ xs
≤ᵘ-refl {ℕ.zero} = inj₂ refl
≤ᵘ-refl {suc n} = inj₂ refl 

≤ᵘ-trans : ∀ {n} {xs ys zs : Binary (suc n)} → xs ≤ᵘ ys → ys ≤ᵘ zs → xs ≤ᵘ zs
≤ᵘ-trans (inj₁ x<y) (inj₁ y<z) = inj₁ (<ᵘ-trans x<y y<z)
≤ᵘ-trans (inj₁ x<y) (inj₂ refl) = inj₁ x<y
≤ᵘ-trans (inj₂ refl) (inj₁ y<z) = inj₁ y<z
≤ᵘ-trans (inj₂ refl) (inj₂ refl) = inj₂ refl

≤ᵘ-antisym : ∀ {n} {xs ys : Binary (suc n)} → xs ≤ᵘ ys → ys ≤ᵘ xs → xs ≡ ys
≤ᵘ-antisym (inj₂ refl) _ = refl
≤ᵘ-antisym _ (inj₂ refl) = refl
≤ᵘ-antisym (inj₁ x<y) (inj₁ y<x) = ⊥-elim (<ᵘ-asym x<y y<x)

≤ᵘ-cons-general : ∀ {n} {x y : Bit} {xs ys : Binary (suc n)} → (x ∷ xs) ≤ᵘ (y ∷ ys) → xs ≤ᵘ ys
≤ᵘ-cons-general (inj₁ lth) with lth
... | lt-tail h = inj₁ h
... | lt-head refl _  = inj₂ refl
≤ᵘ-cons-general (inj₂ refl) = inj₂ refl

≤ᵘ-cons-general-strict : ∀ {n} {x y : Bit} {xs ys : Binary (suc n)}
                       {{_ : y <bᵘ x}}
                       → (x ∷ xs) ≤ᵘ (y ∷ ys)
                       → xs <ᵘ ys
≤ᵘ-cons-general-strict {{lt}} (inj₁ (lt-tail h)) = h
≤ᵘ-cons-general-strict {{lt}} (inj₁ (lt-head refl ()))
≤ᵘ-cons-general-strict {{lt}} (inj₂ ())

≤ᵘ-cons-general' : ∀ {n} {x y : Bit} {xs ys : Binary (suc n)}
                 {{x≤y : x ≤bᵘ y}}
                 → xs ≤ᵘ ys 
                 → (x ∷ xs) ≤ᵘ (y ∷ ys)
≤ᵘ-cons-general' (inj₁ lth) = inj₁ (lt-tail lth)
≤ᵘ-cons-general' {{x≤y}} (inj₂ refl) with x≤y
... | inj₁ h = inj₁ (lt-head refl h)
... | inj₂ refl = inj₂ refl

-- gt
>ᵘ-cons-general : ∀ {n} {x y : Bit} {xs ys : Binary (suc n)} 
                {{_ : x ≤bᵘ y}}
                → (x ∷ xs) >ᵘ (y ∷ ys)
                → xs >ᵘ ys
>ᵘ-cons-general {{inj₁ lt}} gth tail-leh = gth (≤ᵘ-cons-general' tail-leh)
>ᵘ-cons-general {{x≤y}} gth tail-leh = gth (≤ᵘ-cons-general' {{x≤y}} tail-leh)

>ᵘ-cons-general-weak : ∀ {n} {x y : Bit} {xs ys : Binary (suc n)}
                       → (x ∷ xs) >ᵘ (y ∷ ys)
                       → xs ≥ᵘ ys
>ᵘ-cons-general-weak gth tail-lth = gth (inj₁ (lt-tail tail-lth))

>ᵘ-cons-general' : ∀ {n} {x y : Bit} {xs ys : Binary (suc n)}
                 {{x>y : x >bᵘ y}}
                 → xs >ᵘ ys
                 → (x ∷ xs) >ᵘ (y ∷ ys)
>ᵘ-cons-general' {{gt}} tail-gth lte = tail-gth (inj₁ (≤ᵘ-cons-general-strict lte))

-- gte
split-≥ᵘ : ∀ {n} {xs ys : Binary (suc n)} → (xs ≥ᵘ ys) → (xs ≡ ys) ⊎ (xs >ᵘ ys)
split-≥ᵘ {_} {xs} {ys} geh with trichotomyᵘ xs ys
... | tri-lt lth = ⊥-elim (geh lth)
... | tri-eq eqh = inj₁ eqh
... | tri-gt gth = inj₂ gth

-- Mixed
≤ᵘ-<ᵘ-trans : ∀ {n} {xs ys zs : Binary (suc n)} → xs ≤ᵘ ys → ys <ᵘ zs → xs <ᵘ zs
≤ᵘ-<ᵘ-trans (inj₁ x<y) y<z = <ᵘ-trans x<y y<z
≤ᵘ-<ᵘ-trans (inj₂ refl) y<z = y<z

<ᵘ-≤ᵘ-trans : ∀ {n} {xs ys zs : Binary (suc n)} → xs <ᵘ ys → ys ≤ᵘ zs → xs <ᵘ zs
<ᵘ-≤ᵘ-trans x<y (inj₁ y<z) = <ᵘ-trans x<y y<z
<ᵘ-≤ᵘ-trans x<y (inj₂ refl) = x<y

-- Conversion
>ᵘ-to-<ᵘ : ∀ {n} {xs ys : Binary (suc n)} → xs >ᵘ ys → ys <ᵘ xs
>ᵘ-to-<ᵘ {ℕ.zero} {O ∷ []} {O ∷ []} gth = ⊥-elim (gth (inj₂ refl))
>ᵘ-to-<ᵘ {ℕ.zero} {O ∷ []} {I ∷ []} gth = ⊥-elim (gth (inj₁ (lt-head refl lt)))
>ᵘ-to-<ᵘ {ℕ.zero} {I ∷ []} {O ∷ []} gth = lt-head refl lt
>ᵘ-to-<ᵘ {ℕ.zero} {I ∷ []} {I ∷ []} gth = ⊥-elim (gth (inj₂ refl))
>ᵘ-to-<ᵘ {suc n} {O ∷ xs} {O ∷ ys} gth = lt-tail (>ᵘ-to-<ᵘ (λ x≤y → gth (≤ᵘ-cons-general' {{inj₂ refl}} x≤y)))
>ᵘ-to-<ᵘ {suc n} {O ∷ xs} {I ∷ ys} gth = lt-tail (>ᵘ-to-<ᵘ xs>ys)
  where
    xs>ys : xs >ᵘ ys
    xs>ys (inj₁ x<y) = gth (inj₁ (lt-tail x<y))
    xs>ys (inj₂ x≡y) = gth (inj₁ (lt-head x≡y lt))
>ᵘ-to-<ᵘ {suc n} {I ∷ xs} {O ∷ ys} gth with trichotomyᵘ ys xs
... | tri-lt y<x = lt-tail y<x
... | tri-eq y=x = lt-head y=x lt
... | tri-gt y>x = ⊥-elim (gth (inj₁ (lt-tail (>ᵘ-to-<ᵘ y>x))))
>ᵘ-to-<ᵘ {suc n} {I ∷ xs} {I ∷ ys} gth = lt-tail (>ᵘ-to-<ᵘ (λ x≤y → gth (≤ᵘ-cons-general' {{inj₂ refl}} x≤y)))

<ᵘ-to->ᵘ : ∀ {n} {xs ys : Binary (suc n)} → xs <ᵘ ys → ys >ᵘ xs
<ᵘ-to->ᵘ lth (inj₁ gth) = <ᵘ-asym lth gth
<ᵘ-to->ᵘ lth (inj₂ eq) rewrite eq = <ᵘ-irrefl lth

-- Common facts
ones-≥ᵘ-zero : ∀ {n} → ones (suc n) ≥ᵘ Binary.Base.zero (suc n)
ones-≥ᵘ-zero {ℕ.zero} (lt-head _ ())
ones-≥ᵘ-zero {suc n} lth = ones-≥ᵘ-zero (<ᵘ-cons-general lth)

zero-≤ᵘ-all : ∀ {n} (xs : Binary (suc n)) → Binary.Base.zero (suc n) ≤ᵘ xs
zero-≤ᵘ-all {ℕ.zero} (O ∷ []) = inj₂ refl
zero-≤ᵘ-all {ℕ.zero} (I ∷ []) = inj₁ (lt-head refl lt)
zero-≤ᵘ-all {suc n} (O ∷ xs) = ≤ᵘ-cons-general' (zero-≤ᵘ-all xs)
zero-≤ᵘ-all {suc n} (I ∷ xs) = ≤ᵘ-cons-general' (zero-≤ᵘ-all xs)

dec-lt : ∀ {n} {xs : Binary (suc n)} → zero (suc n) <ᵘ xs → dec xs <ᵘ xs
dec-lt {ℕ.zero} {O ∷ []} (lt-head _ ())
dec-lt {ℕ.zero} {I ∷ []} _ = lt-head refl lt
dec-lt {suc n} {O ∷ xs} (lt-tail h) = lt-tail (dec-lt h)
dec-lt {suc n} {O ∷ xs} (lt-head refl ())
dec-lt {suc n} {I ∷ xs} _ = lt-head refl lt

sub->ᵘ-zero : ∀ {n} {xs ys : Binary (suc n)} → xs >ᵘ ys → (xs - ys) >ᵘ zero (suc n)
sub->ᵘ-zero {ℕ.zero} {O ∷ []} {O ∷ []} xs>ys _ = xs>ys (inj₂ refl)
sub->ᵘ-zero {ℕ.zero} {O ∷ []} {I ∷ []} xs>ys _ = xs>ys (inj₁ (lt-head refl lt))
sub->ᵘ-zero {ℕ.zero} {I ∷ []} {O ∷ []} xs>ys = xs>ys
sub->ᵘ-zero {ℕ.zero} {I ∷ []} {I ∷ []} xs>ys _ = xs>ys (inj₂ refl)
sub->ᵘ-zero {suc n} {O ∷ xs} {O ∷ ys} xs>ys (inj₁ (lt-tail lth)) = sub->ᵘ-zero (>ᵘ-cons-general xs>ys) (inj₁ lth)
sub->ᵘ-zero {suc n} {O ∷ xs} {O ∷ ys} xs>ys (inj₁ (lt-head _ ()))
sub->ᵘ-zero {suc n} {O ∷ xs} {O ∷ ys} xs>ys (inj₂ eq) = sub->ᵘ-zero (>ᵘ-cons-general xs>ys) (inj₂ (cong Data.Vec.tail eq))
sub->ᵘ-zero {suc n} {O ∷ xs} {I ∷ ys} xs>ys (inj₁ (lt-tail lth)) = <ᵘ-irrefl (<ᵘ-≤ᵘ-trans lth (zero-≤ᵘ-all _))
sub->ᵘ-zero {suc n} {O ∷ xs} {I ∷ ys} xs>ys (inj₁ (lt-head _ ()))
sub->ᵘ-zero {suc n} {O ∷ xs} {I ∷ ys} xs>ys (inj₂ ())
sub->ᵘ-zero {suc n} {I ∷ xs} {O ∷ ys} xs>ys (inj₁ (lt-tail lth)) = <ᵘ-irrefl (<ᵘ-≤ᵘ-trans lth (zero-≤ᵘ-all _))
sub->ᵘ-zero {suc n} {I ∷ xs} {O ∷ ys} xs>ys (inj₁ (lt-head _ ()))
sub->ᵘ-zero {suc n} {I ∷ xs} {O ∷ ys} xs>ys (inj₂ ())
sub->ᵘ-zero {suc n} {I ∷ xs} {I ∷ ys} xs>ys h rewrite rca-carry-transpose-incʳ xs (~ ys) with h
... | inj₁ (lt-tail lth) = sub->ᵘ-zero (>ᵘ-cons-general xs>ys) (inj₁ lth)
... | inj₁ (lt-head _ ())
... | inj₂ eq = sub->ᵘ-zero (>ᵘ-cons-general xs>ys) (inj₂ (cong Data.Vec.tail eq))

sub-<ᵘ-self : ∀ {n} {xs ys : Binary (suc n)} → xs >ᵘ ys → (xs - ys) ≤ᵘ xs
sub-<ᵘ-self {ℕ.zero} {O ∷ []} {O ∷ []} xs>ys = ⊥-elim (xs>ys (inj₂ refl))
sub-<ᵘ-self {ℕ.zero} {O ∷ []} {I ∷ []} xs>ys = ⊥-elim (xs>ys (inj₁ (lt-head refl lt)))
sub-<ᵘ-self {ℕ.zero} {I ∷ []} {O ∷ []} xs>ys = inj₂ refl
sub-<ᵘ-self {ℕ.zero} {I ∷ []} {I ∷ []} xs>ys = ⊥-elim (xs>ys (inj₂ refl))
sub-<ᵘ-self {suc n} {O ∷ xs} {O ∷ ys} xs>ys = ≤ᵘ-cons-general' (sub-<ᵘ-self (>ᵘ-cons-general xs>ys))
sub-<ᵘ-self {suc n} {I ∷ xs} {O ∷ ys} xs>ys with split-≥ᵘ (>ᵘ-cons-general-weak xs>ys)
... | inj₁ refl rewrite +-elimʳ xs = ≤ᵘ-cons-general' (zero-≤ᵘ-all xs)
... | inj₂ gth = ≤ᵘ-cons-general' (sub-<ᵘ-self gth)
sub-<ᵘ-self {suc n} {I ∷ xs} {I ∷ ys} xs>ys rewrite rca-carry-lift-inc xs (~ ys) 
                                                  | sym (rca-inc-liftʳ xs (~ ys) O) =
    ≤ᵘ-cons-general' (sub-<ᵘ-self (>ᵘ-cons-general xs>ys))
sub-<ᵘ-self {suc n} {O ∷ xs} {I ∷ ys} xs>ys rewrite sym (dec-inc-elim (rca xs (~ ys) O)) | sym (rca-inc-liftʳ xs (~ ys) O) =
    let
      tail-gth = >ᵘ-cons-general xs>ys
      cons-lte = sub-<ᵘ-self tail-gth
      0<diff = >ᵘ-to-<ᵘ (sub->ᵘ-zero tail-gth)
      dec-d<d = dec-lt 0<diff
    in
      inj₁ (lt-tail (<ᵘ-≤ᵘ-trans dec-d<d cons-lte))

-- Logical operation properties
∥-≥ᵘ-left : ∀ {n} {xs ys : Binary (suc n)} → (xs ∥ ys) ≥ᵘ xs
∥-≥ᵘ-left {ℕ.zero} {O ∷ []} {O ∷ []} (lt-head _ ())
∥-≥ᵘ-left {ℕ.zero} {O ∷ []} {I ∷ []} (lt-head _ ())
∥-≥ᵘ-left {ℕ.zero} {I ∷ []} {O ∷ []} (lt-head _ ())
∥-≥ᵘ-left {ℕ.zero} {I ∷ []} {I ∷ []} (lt-head _ ())
∥-≥ᵘ-left {suc n} {x ∷ xs} {y ∷ ys} (lt-tail lth) = ∥-≥ᵘ-left lth
∥-≥ᵘ-left {suc n} {O ∷ xs} {y ∷ ys} (lt-head _ ())
∥-≥ᵘ-left {suc n} {I ∷ xs} {y ∷ ys} (lt-head _ ())

∥-≥ᵘ-right : ∀ {n} {xs ys : Binary (suc n)} → (xs ∥ ys) ≥ᵘ ys
∥-≥ᵘ-right {ℕ.zero} {O ∷ []} {O ∷ []} (lt-head _ ())
∥-≥ᵘ-right {ℕ.zero} {O ∷ []} {I ∷ []} (lt-head _ ())
∥-≥ᵘ-right {ℕ.zero} {I ∷ []} {O ∷ []} (lt-head _ ())
∥-≥ᵘ-right {ℕ.zero} {I ∷ []} {I ∷ []} (lt-head _ ())
∥-≥ᵘ-right {suc n} {x ∷ xs} {y ∷ ys} (lt-tail lth) = ∥-≥ᵘ-right lth
∥-≥ᵘ-right {suc n} {O ∷ xs} {y ∷ ys} (lt-head _ ())
∥-≥ᵘ-right {suc n} {I ∷ xs} {y ∷ ys} (lt-head _ ())

&-≤ᵘ-left : ∀ {n} {xs ys : Binary (suc n)} → (xs & ys) ≤ᵘ xs
&-≤ᵘ-left {ℕ.zero} {O ∷ []} {O ∷ []} = inj₂ refl
&-≤ᵘ-left {ℕ.zero} {O ∷ []} {I ∷ []} = inj₂ refl
&-≤ᵘ-left {ℕ.zero} {I ∷ []} {O ∷ []} = inj₁ (lt-head refl lt)
&-≤ᵘ-left {ℕ.zero} {I ∷ []} {I ∷ []} = inj₂ refl
&-≤ᵘ-left {suc n} {O ∷ xs} {y ∷ ys} with &-≤ᵘ-left {n} {xs} {ys}
... | inj₁ lth = inj₁ (lt-tail lth)
... | inj₂ eq = inj₂ (cong (O ∷_) eq)
&-≤ᵘ-left {suc n} {I ∷ xs} {y ∷ ys} with &-≤ᵘ-left {n} {xs} {ys}
... | inj₁ lth = inj₁ (lt-tail lth)
... | inj₂ eq with y
...   | O = inj₁ (lt-head eq lt)
...   | I = inj₂ (cong (I ∷_) eq)

&-≤ᵘ-right : ∀ {n} {xs ys : Binary (suc n)} → (xs & ys) ≤ᵘ ys
&-≤ᵘ-right {ℕ.zero} {O ∷ []} {O ∷ []} = inj₂ refl
&-≤ᵘ-right {ℕ.zero} {O ∷ []} {I ∷ []} = inj₁ (lt-head refl lt)
&-≤ᵘ-right {ℕ.zero} {I ∷ []} {O ∷ []} = inj₂ refl
&-≤ᵘ-right {ℕ.zero} {I ∷ []} {I ∷ []} = inj₂ refl
&-≤ᵘ-right {suc n} {O ∷ xs} {y ∷ ys} with &-≤ᵘ-right {n} {xs} {ys}
... | inj₁ lth = inj₁ (lt-tail lth)
... | inj₂ eq with y
...   | O = inj₂ (cong (O ∷_) eq)
...   | I = inj₁ (lt-head eq lt)
&-≤ᵘ-right {suc n} {I ∷ xs} {y ∷ ys} with &-≤ᵘ-right {n} {xs} {ys}
... | inj₁ lth = inj₁ (lt-tail lth)
... | inj₂ eq = inj₂ (cong (y ∷_) eq)

+-<ᵘ-inc : ∀ {n} {xs ys : Binary (suc n)} → AddNotMax xs ys → (xs + ys) <ᵘ inc (xs + ys)
+-<ᵘ-inc {ℕ.zero} {O ∷ []} {O ∷ []} snoh = snoh
+-<ᵘ-inc {ℕ.zero} {I ∷ []} {O ∷ []} (lt-head _ ())
+-<ᵘ-inc {ℕ.zero} {O ∷ []} {I ∷ []} (lt-head _ ())
+-<ᵘ-inc {ℕ.zero} {I ∷ []} {I ∷ []} snoh = lt-head refl lt
+-<ᵘ-inc {suc n} {O ∷ xs} {O ∷ ys} snoh = lt-head refl lt
+-<ᵘ-inc {suc n} {I ∷ xs} {O ∷ ys} (lt-tail lth) = lt-tail (+-<ᵘ-inc lth)
+-<ᵘ-inc {suc n} {I ∷ xs} {O ∷ ys} (lt-head _ ())
+-<ᵘ-inc {suc n} {O ∷ xs} {I ∷ ys} (lt-tail lth) = lt-tail (+-<ᵘ-inc lth)
+-<ᵘ-inc {suc n} {O ∷ xs} {I ∷ ys} (lt-head _ ())
+-<ᵘ-inc {suc n} {I ∷ xs} {I ∷ ys} snoh = lt-head refl lt

inc-≤ᵘ-max : ∀ {n} {xs : Binary (suc n)} → xs <ᵘ ones (suc n) → inc xs ≤ᵘ ones (suc n)
inc-≤ᵘ-max {ℕ.zero} {O ∷ []} h = inj₂ refl
inc-≤ᵘ-max {ℕ.zero} {I ∷ []} h = inj₁ (lt-head refl lt)
inc-≤ᵘ-max {suc n} {O ∷ xs} (lt-tail lth) = inj₁ (lt-tail lth)
inc-≤ᵘ-max {suc n} {O ∷ xs} (lt-head refl lt) = inj₂ refl
inc-≤ᵘ-max {suc n} {I ∷ xs} (lt-tail lth) with inc-≤ᵘ-max lth
... | inj₁ lth = inj₁ (lt-tail lth)
... | inj₂ eqh = inj₁ (lt-head eqh lt)

+-no-overflow : ∀ {n} {xs ys : Binary (suc n)} → AddNotMax xs ys → (xs + ys) <ᵘ ones (suc n)
+-no-overflow {ℕ.zero} {O ∷ []} {O ∷ []} snoh = snoh
+-no-overflow {ℕ.zero} {I ∷ []} {O ∷ []} (lt-head _ ())
+-no-overflow {ℕ.zero} {O ∷ []} {I ∷ []} snoh = snoh
+-no-overflow {ℕ.zero} {I ∷ []} {I ∷ []} snoh = lt-head refl lt
+-no-overflow {suc n} {O ∷ xs} {O ∷ ys} (lt-tail lth) = lt-tail (+-no-overflow lth)
+-no-overflow {suc n} {O ∷ xs} {O ∷ ys} (lt-head ys≡~xs lt) = lt-head (trans (cong (xs +_) ys≡~xs) (~-+-ones xs)) lt
+-no-overflow {suc n} {I ∷ xs} {O ∷ ys} (lt-tail lth) = lt-tail (+-no-overflow lth)
+-no-overflow {suc n} {I ∷ xs} {O ∷ ys} (lt-head _ ())
+-no-overflow {suc n} {O ∷ xs} {I ∷ ys} (lt-tail lth) = lt-tail (+-no-overflow lth)
+-no-overflow {suc n} {O ∷ xs} {I ∷ ys} (lt-head _ ())
+-no-overflow {suc n} {I ∷ xs} {I ∷ ys} (lt-tail lth) with inc-≤ᵘ-max (+-no-overflow lth)
... | inj₁ lth rewrite rca-carry-lift-inc xs ys = lt-tail lth
... | inj₂ eqh = lt-head (trans (rca-carry-lift-inc xs ys) eqh) lt
+-no-overflow {suc n} {I ∷ xs} {I ∷ ys} (lt-head _ ())

-- Signed properties
-- lt

-- lte
≤-cons-general : ∀ {n} {x y : Bit} {xs ys : Binary (suc n)} → (x ∷ xs) ≤ (y ∷ ys) → xs ≤ ys
≤-cons-general {n} {x} {y} {xs} {ys} (inj₁ lth) with signBit xs | signBit ys
... | O | O = <ᵘ-cons-general-weak lth
... | O | I = inj₁ lth
... | I | O = inj₁ Data.Unit.tt
... | I | I = <ᵘ-cons-general-weak lth
≤-cons-general {n} {x} {y} {xs} {ys} (inj₂ refl) = inj₂ refl

-- gt

-- gte
