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

open is-apartness
```
-->

```agda
module Algebra.Ring.Field {ℓ} (R : Ring ℓ) where
```

<!--
```agda
open Re R

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

We begin with the weaker notion of a **local ring**. These are
nontrivial rings with the property that $x + y = 1$ implies $x$ is
invertible or $y$ is invertible.

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
  #-is-apartness .irrefl = subst (λ x → ¬(is-invertible x))
    (sym +-invr) (0≠1 ∘ 0-invertible→0≡1)
 ```

Cotransitivity follows from `locality`{.Agda} as follows. Let $x,y,z :
R$, and suppose $x-z = (x-y)-(y-z)$ is invertible with inverse $a$. Then
$(x-y)a + (y-z)a = 1$, so one of the terms is invertible, say $(x-y)a$.
It then follows from the `2-out-of-3`{.Agda ident="invertible-cancell"}
property that $x-y$ is invertible.

```agda
  #-is-apartness .cotrans {x} {y} {z} x#z = join-map
    (λ inv₁ → invertible-cancell (unit→invertible u invertible⁻¹) inv₁)
    (λ inv₁ → invertible-cancell (unit→invertible u invertible⁻¹) inv₁)
    (locality q)
    where
      p : ∀ (grp : Group-on X) {a b c}
        → let open Group-on grp
          in a ⋆ c ≡ (a ⋆ inverse b) ⋆ (b ⋆ c)
      p grp = group-on! grp

      u : Unit
      u = invertible→unit ((x - y) + (y - z)) $
        subst is-invertible (p (additive-group .snd)) x#z

      q : (x - y) * u .from + (y - z) * u .from ≡ 1r
      q =
        (x - y) * u .from + (y - z) * u .from ≡˘⟨ *-distribr ⟩
        ((x - y) + (y - z)) * u .from         ≡⟨ u .Unit.invl ⟩
        1r                                    ∎

  #-is-apartness .symᵃ x#y = subst is-invertible
    (p (additive-group .snd)) (neg-invertible x#y)
    where
      p : ∀ (grp : Group-on X) {x y}
        → let open Group-on grp
          in inverse (x ⋆ inverse y) ≡ y ⋆ inverse x
      p grp = group-on! grp

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
a discrete skewfield is a nontrivial ring for which every element is
either zero or invertible.

```agda
record is-discrete-skewfield : Type ℓ where
  no-eta-equality
  field
    0≠1 : 0r ≠ 1r
    invertible? : ∀ x → is-invertible x ⊎ x ≡ 0r

  locality : ∀ {x y} → x + y ≡ 1r → (is-invertible x) ∗ (is-invertible y)
  locality {x} {y} p with invertible? x
  ...                | inl inv = inl inv
  ...                | inr x≡0 =
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

  open is-skewfield has-is-skew-field hiding (locality ; ¬invertible→0) public

  #-is-decidable : Tight-apartness.is-decidable tight-apartness
  #-is-decidable x y = ⊎-map id
    (λ p → monoid-inverse-unique a.has-is-monoid _ _ _ p a.inversel)
    $ invertible? (x - y)
```

A **field** (resp. **discrete field**) is simply a commutative skewfield
(discrete skewfield).

```agda
is-field = is-commutative-ring R × is-skewfield
is-discrete-field = is-commutative-ring R × is-discrete-skewfield
```
