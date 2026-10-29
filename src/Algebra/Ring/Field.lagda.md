<!--
```agda
open import Algebra.Group.Solver
open import Algebra.Group
open import Algebra.Monoid
open import Algebra.Ring.Commutative
open import Algebra.Ring

open import Homotopy.Join

open import Data.Apartness
open import Data.Sum

open import 1Lab.Prelude hiding (_-_ ; _+_ ; _*_)

import Algebra.Ring.Element as Re
import Algebra.Group.Reasoning as Gr

open is-apartness
```
-->

```agda
module Algebra.Ring.Field where
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

# Local rings and fields

In classical mathematics, a ring is called a skewfield if all its
nonzero elements are invertible. Constructively this doesn't get us very
far, as denial inequality just isn't that useful. We would like our
fields to be equipped with tight apartness relations so that elements
_apart_ from zero are invertible.

We begin with the weaker notion of a **local ring**. These are nonzero
rings with the property that $x + y = 1$ implies $x$ is invertible or
$y$ is invertible.

```agda
  record is-local : Type ℓ where
    no-eta-equality
    field
      0≠1 : 0r ≠ 1r
      locality : ∀ {x y} → x + y ≡ 1r → (is-invertible x) ∗ (is-invertible y)
```

These properties give us exactly what we need to show that

```agda
    _#_ : ⌞ R ⌟ → ⌞ R ⌟ → Type ℓ
    x # y = is-invertible (x - y)
```

is an [[apartness relation]].

```agda
    #-is-apartness : is-apartness _#_
    #-is-apartness .has-is-prop = is-invertible-is-prop
```

Irreflexivity follows from `nontriviality`{.Agda ident="0≠1"}.

```agda
    #-is-apartness .irrefl x = 0≠1 $ 0-invertible→0≡1 $ subst is-invertible +-invr x
```

Cotransitivity follows from `locality`{.Agda} as follows. Let $x,y,z :
R$, and suppose $x-z = (x-y)+(y-z)$ is invertible with inverse $a$. Then
$(x-y)a + (y-z)a = 1$, so one of the terms is invertible, say $(x-y)a$.
It then follows from the `2-out-of-3`{.Agda ident="invertible-cancell"}
property that $x-y$ is invertible.

```agda
    #-is-apartness .cotrans {x} {y} {z} x#z = join-map
      (λ inv₁ → invertible-cancell (unit→invertible u invertible⁻¹) inv₁)
      (λ inv₁ → invertible-cancell (unit→invertible u invertible⁻¹) inv₁)
      (locality p)
      where
        u : Unit
        u = invertible→unit ((x - y) + (y - z))
          $ subst is-invertible diff≡diff*diff x#z

        p : (x - y) * u .from + (y - z) * u .from ≡ 1r
        p =
          (x - y) * u .from + (y - z) * u .from ≡˘⟨ *-distribr ⟩
          ((x - y) + (y - z)) * u .from         ≡⟨ u .Unit.invl ⟩
          1r                                    ∎

    #-is-apartness .symᵃ x#y = subst is-invertible inverse-diff (neg-invertible x#y)

    apartness : Apartness ⌞ R ⌟ ℓ
    apartness = to-apartness #-is-apartness
```

A local ring is called a (Heyting) **skewfield** iff the canonical
apartness relation `_#_`{.Agda} is `tight`{.Agda ident="#-is-tight"}.
Equivalently, every noninvertible element is equal to zero.

```agda
  record is-skewfield : Type ℓ where
    no-eta-equality
    field
      has-is-local : is-local
      ¬invertible→0 : ∀ {x} → ¬(is-invertible x) → x ≡ 0r

    open is-local has-is-local public

    #-is-tight : is-tight _#_
    #-is-tight ¬x#y = monoid-inverse-unique a.has-is-monoid _ _ _
      (¬invertible→0 ¬x#y) a.inversel

    tight-apartness = to-tight-apartness #-is-apartness #-is-tight
```

A **discrete skewfield** is a skewfield for which this apartness
relation is `decidable`{.Agda ident="#-is-decidable"}. Equivalently,
a discrete skewfield is a nontrivial ring in which every element is
either zero or invertible.

```agda
  record is-discrete-skewfield : Type ℓ where
    no-eta-equality
    field
      0≠1 : 0r ≠ 1r
      invertible? : ∀ x → is-invertible x ⊎ x ≡ 0r

    locality : ∀ {x y} → x + y ≡ 1r → (is-invertible x) ∗ (is-invertible y)
    locality {x} {y} p with invertible? x
    ...                     | inl inv = inl inv
    ...                     | inr x≡0 =
      let 1≡y = 1r     ≡˘⟨ p ⟩
                x + y  ≡⟨ ap (_+ y) x≡0 ⟩
                0r + y ≡⟨ a.idl ⟩
                y      ∎
      in inr (subst is-invertible 1≡y 1-invertible)

    ¬invertible→0 : ∀ {x} → ¬(is-invertible x) → x ≡ 0r
    ¬invertible→0 {x} ¬inv with invertible? x
    ...                       | inl inv = absurd (¬inv inv)
    ...                       | inr x≡0 = x≡0

    has-is-skew-field : is-skewfield
    has-is-skew-field = record
      { has-is-local = record { 0≠1 = 0≠1 ; locality = locality }
      ; ¬invertible→0 = ¬invertible→0 }

    open is-skewfield has-is-skew-field hiding (0≠1 ; locality ; ¬invertible→0) public

    #-is-decidable : Tight-apartness.is-decidable tight-apartness
    #-is-decidable x y = ⊎-map id zero-diff $ invertible? (x - y)
```


<!--
```agda
  0≠1→invertible?-is-prop
    : 0r ≠ 1r
    → ∀ x → is-prop (is-invertible x ⊎ x ≡ 0r)
  0≠1→invertible?-is-prop 0≠1 x = disjoint-⊎-is-prop is-invertible-is-prop (has-is-set x 0r)
    λ (x-inv , x≡0) → 0≠1 $ 0-invertible→0≡1 $ subst is-invertible x≡0 x-inv
```
-->


A **field** (resp. **discrete field**) is simply a commutative skewfield
(discrete skewfield).

<!--
```agda
open CRing
```
-->

```agda
is-field : ∀ {ℓ} → CRing ℓ → Type ℓ
is-field R = is-skewfield (ring R)

is-discrete-field : ∀ {ℓ} → CRing ℓ → Type ℓ
is-discrete-field R = is-discrete-skewfield (ring R)
```
