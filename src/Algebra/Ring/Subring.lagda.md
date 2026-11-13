<!--
```agda
open import Algebra.Monoid.Submonoid
open import Algebra.Group.Subgroup
open import Algebra.Group.Ab
open import Algebra.Monoid
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude hiding (_*_ ; _+_)

open import Data.Power

import Cat.Displayed.Instances.Subobjects
```
-->

```agda
module Algebra.Ring.Subring where
```

<!--
```agda
private variable
  ℓ : Level
  R S : Ring ℓ 
private module _ {ℓ} where open Cat.Displayed.Instances.Subobjects (Rings ℓ) hiding (to ; from) public
```
-->

# Subrings

A **subring** $m$ of a ring $R$ is a [[monomorphism]] $S \xto{m} R$,
that is, an object of the [[poset of subobjects]] $\Sub(G)$. Just as
for [[subgroups]], one can adopt the alternate point of view that a
subring is a special kind of predicate $R \to \prop$.

```agda
Subring : Ring ℓ → Type (lsuc ℓ)
Subring {ℓ = ℓ} = Subobject
```

A predicate $H : G \to \prop$ of a group represents a subring if it
represents both an additive [[subgroup]] and a multiplicative
[[monoid]].

```agda
record represents-subring (R : Ring ℓ) (S : ℙ ⌞ R ⌟) : Type ℓ where
  open Ring-on (R .snd)
  field
    has-subgroup : represents-subgroup additive-group S
    has-submonoid : represents-submonoid multiplicative-monoid S

  open represents-subgroup has-subgroup renaming
    (has-⋆ to has-+ ; has-unit to has-0 ; has-inv to has-neg ) public
  open represents-submonoid has-submonoid renaming
    (has-⋆ to has-* ; has-id to has-1) public
```

If $S$ represents a subring, then its total space inherits a ring
structure from $R$ so that the first projection $\int_p S \xto{m} R$ is
a ring homomorphism.

```agda
rep-subring→ring-on
  : {R : Ring ℓ} (S : ℙ ⌞ R ⌟) → represents-subring R S
  → Ring-on (∫ₚ S)
rep-subring→ring-on {R = R} S sr =
  let
    open represents-subring sr
    open Ring-on (R .snd) using (*-distribl ; *-distribr ; +-commutes)
    open Group-on (rep-subgroup→group-on S has-subgroup) renaming (_⋆_ to _+_)
    open Monoid-on (rep-submonoid→monoid-on S has-submonoid) renaming
      (identity to 1r ; _⋆_ to _*_ ; has-is-monoid to *-monoid)
  in λ where
    .Ring-on.1r → 1r
    .Ring-on._*_ → _*_
    .Ring-on._+_ → _+_
    .Ring-on.has-is-ring → λ where
      .is-ring.+-group → λ where
        .is-abelian-group.has-is-group → has-is-group
        .is-abelian-group.commutes → Σ-prop-path! +-commutes
      .is-ring.*-monoid → *-monoid
      .is-ring.*-distribl → Σ-prop-path! *-distribl
      .is-ring.*-distribr → Σ-prop-path! *-distribr

predicate→subring
  : {R : Ring ℓ} (S : ℙ ⌞ R ⌟) → represents-subring R S
  → Subring R
predicate→subring {R = R} S sr = record { map = it ; monic = ism } where
  it : Rings.Hom (el! _ , (rep-subring→ring-on S sr)) R
  it .fst = fst
  it .snd .is-ring-hom.pres-* _ _ = refl
  it .snd .is-ring-hom.pres-id = refl
  it .snd .is-ring-hom.pres-+ _ _ = refl

  ism : Rings.is-monic it
  ism = Homomorphism-monic it Σ-prop-path!
```
