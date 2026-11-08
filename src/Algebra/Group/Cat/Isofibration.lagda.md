
<!--
```agda
open import Algebra.Monoid.Cat.Isofibration
open import Algebra.Monoid
open import Algebra.Group

open import Cat.Displayed.Isofibration
open import Cat.Instances.Sets
open import Cat.Prelude

import Cat.Displayed.Morphism as Dm
import Cat.Morphism as Cm
```
-->

```agda
module Algebra.Group.Cat.Isofibration (ℓ : Level) where
```

<!--
```agda
private
  module Sets = Cm (Sets ℓ)
  module Mons where
    open Isofibration (Monoids-isofibration ℓ) public
    open Dm (Monoids-on ℓ) public

open Dm (Groups-on ℓ)

_ = is-category→isofibration

open is-group-hom
```
-->

# The groups isofibration {defines="groups-isofibration"}

Since $\Sets_\kappa$ is a category, $\Grp_\kappa \liesover \Sets_\kappa$
is `automatically`{.Agda ident=is-category→isofibration} an
[[isofibration]]. For technical reasons it is nonetheless desirable to
have a bespoke but equivalent implementation of this fact, which we give
here.

```agda
private module _ {A B} (e≅ : A Sets.≅ B) (Aᵍ : Group-on ⌞ A ⌟) where
  e = iso→equiv e≅
  open Equiv
  module A = Group-on Aᵍ
```

Suppose $A$ is a set with the structure of a group and $e : A \simeq
B$ is an equivalence of sets. Using the [[monoids isofibration]], we
can transport monoid structure on $A$ to a monoid structure on $B$,
which in turn accounts for most of the group structure on $B$.

```agda
  Aᵐ : Monoid-on ⌞ A ⌟
  Aᵐ = A.underlying-monoid .snd

  Bᵐ : Monoid-on ⌞ B ⌟
  Bᵐ = e≅ Mons.^* Aᵐ
  module B = Monoid-on Bᵐ

  Aᵐ≅Bᵐ : Aᵐ Mons.≅[ e≅ ] Bᵐ
  Aᵐ≅Bᵐ = Mons.^*-lifts e≅ Aᵐ

  Bᵍ : Group-on ⌞ B ⌟
  Bᵍ = to-group-on λ where
    .make-group.group-is-set → B.has-is-set
    .make-group.mul → B._⋆_
    .make-group.unit → B.identity
    .make-group.assoc _ _ _ → B.associative
    .make-group.idl _ → B.idl
```

All thats left to do ourselves are the inverses in $B$.

```agda
    .make-group.inv x → e .to (A.inverse (e .from x))
    .make-group.invl → EquivJ
      (λ B e → ∀ x
        → (e .to (e .from (e .to (A.inverse (e .from x))) A.⋆ (e .from x))) ≡ (e .to A.unit))
       (λ _ → A.inversel) e
```

Since group homomorphisms are just monoid homomorphisms between
underlying monoids, we can turn `Aᵐ≅Bᵐ`{.Agda} into a group isomorphism
`Aᵍ≅Bᵍ`{.Agda}.

```agda
  Aᵍ→Bᵍ : is-group-hom Aᵍ Bᵍ (e .to)
  Aᵍ→Bᵍ .pres-⋆ = Aᵐ≅Bᵐ .Mons.to' .is-monoid-hom.pres-⋆
  
  Bᵍ→Aᵍ : is-group-hom Bᵍ Aᵍ (e .from)
  Bᵍ→Aᵍ .pres-⋆ = Aᵐ≅Bᵐ .Mons.from' .is-monoid-hom.pres-⋆

  Aᵍ≅Bᵍ : Aᵍ ≅[ e≅ ] Bᵍ
  Aᵍ≅Bᵍ = make-iso[ e≅ ] Aᵍ→Bᵍ Bᵍ→Aᵍ prop! prop!
```

Together these give us exactly what we need to show groups form an
isofibration over sets.

```agda
Groups-isofibration : Isofibration (Groups-on ℓ)
Groups-isofibration = record { _^*_ = Bᵍ ; ^*-lifts = Aᵍ≅Bᵍ }
```
