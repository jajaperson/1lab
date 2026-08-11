<!--
```agda
open import 1Lab.Prelude hiding (_+_ ; _*_)

open import Algebra.Ring
```
-->

```agda
module Algebra.Ring.Instances.Lift where
```

# Lifting rings across universes

Suppose you have a [[ring]] $R$ in universe $\ell$, when you really want
a ring in universe $\ell \sqcup \ell'$. Fortunately this turns out to be
quite routine.

```agda
Lift-ring-on : ∀ {ℓ} {R : Type ℓ} ℓ' → Ring-on R → Ring-on (Lift ℓ' R)
Lift-ring-on {R = R} ℓ Rᴿ = to-ring-on mr where
  module R = Ring-on Rᴿ
  open make-ring
  mr : make-ring _
  mr .ring-is-set                           = hlevel 2
  mr .1R                                    = lift (R.1r)
  mr .0R                                    = lift (R.0r)
  mr .-_         (lift x)                   = lift (R.- x)
  mr ._+_        (lift x) (lift y)          = lift (x R.+ y)
  mr ._*_        (lift x) (lift y)          = lift (x R.* y)
  mr .*-idl      (lift x)                   = ap lift $ R.*-idl
  mr .*-idr      (lift x)                   = ap lift $ R.*-idr
  mr .+-idl      (lift x)                   = ap lift $ R.a.idl
  mr .+-invr     (lift x)                   = ap lift $ R.a.inverser
  mr .+-comm     (lift x) (lift y)          = ap lift $ R.a.commutes
  mr .+-assoc    (lift x) (lift y) (lift z) = ap lift $ R.a.associative
  mr .*-assoc    (lift x) (lift y) (lift z) = ap lift $ R.*-associative
  mr .*-distribl (lift x) (lift y) (lift z) = ap lift $ R.*-distribl
  mr .*-distribr (lift x) (lift y) (lift z) = ap lift $ R.*-distribr

Lift-ring : ∀ {ℓ} ℓ' → Ring ℓ → Ring (ℓ' ⊔ ℓ)
Lift-ring ℓ' (R , Rᴿ) = el! (Lift ℓ' ⌞ R ⌟) , Lift-ring-on ℓ' Rᴿ
```

We can also do the same for ring homomorphisms, either lifting the
domain or the codomain.

<!--
```agda
open is-ring-hom
```
-->

```agda
Lift-ring-hom-l
  : ∀ {a b a'} {A : Type a} {Aᴿ : Ring-on A} {B : Type b} {Bᴿ : Ring-on B} {f}
  → is-ring-hom Aᴿ Bᴿ f
  → is-ring-hom (Lift-ring-on a' Aᴿ) Bᴿ (f ∘ lower)
Lift-ring-hom-l f-hom .pres-id                  = f-hom .pres-id
Lift-ring-hom-l f-hom .pres-* (lift x) (lift y) = f-hom .pres-* x y
Lift-ring-hom-l f-hom .pres-+ (lift x) (lift y) = f-hom .pres-+ x y

Lift-ring-hom-r
  : ∀ {a b b'} {A : Type a} {Aᴿ : Ring-on A} {B : Type b} {Bᴿ : Ring-on B} {f}
  → is-ring-hom Aᴿ Bᴿ f
  → is-ring-hom Aᴿ (Lift-ring-on b' Bᴿ) (lift ∘ f)
Lift-ring-hom-r f-hom .pres-id    = ap lift $ f-hom .pres-id
Lift-ring-hom-r f-hom .pres-* x y = ap lift $ f-hom .pres-* x y
Lift-ring-hom-r f-hom .pres-+ x y = ap lift $ f-hom .pres-+ x y
```
