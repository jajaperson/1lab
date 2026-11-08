<!--
```agda
open import Algebra.Monoid
open import Algebra.Group

open import Cat.Displayed.Functor.Properties.Total
open import Cat.Displayed.Functor.Properties
open import Cat.Displayed.Univalence.Thin
open import Cat.Displayed.Functor.Total
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Prelude
```
-->

```agda
module Algebra.Group.Cat.ForgetInverses (ℓ : Level) where
```

<!--
```agda
private
  Mon = Monoids ℓ
  Grp = Groups ℓ
  Mon[] = Monoids-on ℓ
  Grp[] = Groups-on ℓ
  module Mon[] = Displayed Mon[]
  module Grp[] = Displayed Grp[]

open Displayed-functor
open Group-on
```
-->

# The forgetful functor from groups to monoids

Since every group has an `underlying-monoid`{.Agda}, and these are
preserved by group homomorphisms, there is a canonical functor
$\Grp_\kappa \to \thecat{Mon}_\kappa$ which forgets the inverses of
group elements. We can construct this as a [[vertical functor]] between
the corresponding displayed categories.

```agda
Forget-inverses[] : Vertical-functor Grp[] Mon[]
Forget-inverses[] = λ where
  .F₀' G  → underlying-monoid G .snd
  .F₁' fᵍ → λ where
    .is-monoid-hom.pres-⋆  → is-group-hom.pres-⋆ fᵍ
    .is-monoid-hom.pres-id → is-group-hom.pres-id fᵍ
  .F-id' → prop!
  .F-∘'  → prop!
```

In fact, a group homomorphism $G \to H$ is _precisely_ a monoid
homomorphism of the unerlying monoids, so this functor is [[fully
faithful]].

```agda
Forget-inverses-ff[] : is-ff[] Forget-inverses[]
Forget-inverses-ff[] {a} {b} = biimp-is-equiv! _
  λ where x .is-group-hom.pres-⋆ → x .is-monoid-hom.pres-⋆
```

Finally, we take the total functor. 

```agda
Forget-inverses : Functor Grp Mon
Forget-inverses = ∫ᶠ↓ Forget-inverses[]

Forget-inverses-ff : is-fully-faithful Forget-inverses
Forget-inverses-ff = ∫-ff Forget-inverses[] id-equiv
  λ {x} {y} → Forget-inverses-ff[] {x} {y}
```

