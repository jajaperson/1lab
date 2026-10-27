<!--
```agda
open import Algebra.Group.Solver
open import Algebra.Group
open import Algebra.Monoid
open import Algebra.Ring.Commutative
open import Algebra.Ring

open import Homotopy.Join

open import Data.Set.Apartness
open import Data.Sum

open import 1Lab.Prelude hiding (_-_ ; _+_ ; _*_)

import Algebra.Ring.Element as Re
import Algebra.Group.Reasoning as Gr

open is-apartness
```
-->

```agda
module Algebra.Ring.Cancellative where
```

<!--
```agda
module _ {ℓ} (R : Ring ℓ) where
  open Re R
  open Ring-on (R .snd)
  open Gr (additive-group .snd)

  variable
    ℓ' : Level
    X : Type ℓ'
```
-->

# Cancellative rings and integral domains

In classical mathematics, an integral domain is defined as a
(commutative) ring without zero divisors. In constructive mathematics
a positive formulation is more workable.

Recall that an element $a : R$ is `cancellable`{.Agda ident="is-cancellable"}
iff $ax = ay$ or $xa = ya$ implies $x = y$, i.e. $a$ is both monic and
epic. Classically, an element of a nonzero ring is cancellable iff it is
not a zero divisor.

:::{.definition #approximate-cancellative-ring}
An **approximate cancellative ring** is a nonzero ring for which being
callencable is _coadditive_, i.e. $x + y$ being cancellable implies
either $x$ or $y$ is cancellable.
:::

```agda
  record is-approx-cancellative : Type ℓ where
    no-eta-equality
    field
      0≠1 : 0r ≠ 1r
      cancellable-+ᶜ : ∀ {x y} → is-cancellable (x + y)
                     → (is-cancellable x) ∗ (is-cancellable y)
```

These properties give us exactly what we need for

```agda
    _#_ : ⌞ R ⌟ → ⌞ R ⌟ → Type ℓ
    x # y = is-cancellable (x - y)
```

to be an [[apartness relation]].

```agda
    #-is-apartness : is-apartness _#_
    #-is-apartness .has-is-prop = is-cancellable-is-prop _
    #-is-apartness .irrefl x = 0≠1 $ 0-cancellable→0≡1 $ subst is-cancellable +-invr x
    #-is-apartness .cotrans x#z = cancellable-+ᶜ $ subst is-cancellable diff≡diff*diff x#z
    #-is-apartness .symᵃ {x} {y} x#y = subst is-cancellable inverse-diff $ neg-cancellable x#y
```

:::{.definition #cancellative-ring}
A **cancellative ring** has the additional property that $0$ is the only
non-cancellative element. Equivalently, `_#_`{.Agda} is a [[tight
apartness relation]].
:::

```agda
  record is-cancellative : Type ℓ where
    no-eta-equality
    field
      has-is-approx : is-approx-cancellative
      ¬cancellable→0 : ∀ {x} → ¬(is-cancellable x) → x ≡ 0r

    open is-approx-cancellative has-is-approx public

    #-is-tight : is-tight _#_
    #-is-tight ¬x#y = zero-diff (¬cancellable→0 ¬x#y)

    tight-apartness = to-tight-apartness #-is-apartness #-is-tight
```

A **discrete cancellative ring** is a cancellative ring for which this
apartnesws relation is `decidable`{.Agda ident="#-is-decidable"}.
Equivalently, a discrete cancellative ring is a nontrivial ring in which
every element is either zero or cancellable.

```agda
  record is-discrete-cancellative : Type ℓ where
    no-eta-equality
    field
      0≠1 : 0r ≠ 1r
      cancellable? : ∀ x → is-cancellable x ⊎ x ≡ 0r

    cancellable-+ᶜ : ∀ {x y} → is-cancellable (x + y)
                   → (is-cancellable x) ∗ (is-cancellable y)
    cancellable-+ᶜ {x} {y} x+yᶜ with cancellable? x
    ...                            | inl xᶜ = inl xᶜ
    ...                            | inr x≡0 = inr
      (subst is-cancellable ((ap (_+ y) x≡0) ∙ +-idl) x+yᶜ)

    ¬cancellable→0 : ∀ {x} → ¬(is-cancellable x) → x ≡ 0r
    ¬cancellable→0 {x} ¬xᶜ with cancellable? x
    ...                       | inl xᶜ = absurd (¬xᶜ xᶜ)
    ...                       | inr x≡0 = x≡0

    has-is-cancellative : is-cancellative
    has-is-cancellative = record
      { has-is-approx = record { 0≠1 = 0≠1 ; cancellable-+ᶜ = cancellable-+ᶜ }
      ; ¬cancellable→0 = ¬cancellable→0
      }

    open is-cancellative has-is-cancellative hiding (0≠1 ; cancellable-+ᶜ ; ¬cancellable→0) public

    #-is-decidable : Tight-apartness.is-decidable tight-apartness
    #-is-decidable x y = ⊎-map id zero-diff $ cancellable? (x - y)
```


:::{.definition #integral-domain alias="approximate-integral-domain"}
A commutative cancellative ring (resp. approximate, discrete) is called
an **integral domain** (resp. approximate, discrete).[^domain]
:::

<!--
```agda
open CRing using (ring)
```
-->

```agda
is-approx-integral-domain : ∀ {ℓ} → CRing ℓ → Type ℓ
is-approx-integral-domain R = is-approx-cancellative (ring R)

is-integral-domain : ∀ {ℓ} → CRing ℓ → Type ℓ
is-integral-domain R = is-cancellative (ring R)

is-discrete-integral-domain : ∀ {ℓ} → CRing ℓ → Type ℓ
is-discrete-integral-domain R = is-discrete-cancellative (ring R)
```

[^domain]: Unrelated to domain theory.
