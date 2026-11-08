
<!--
```agda
open import Algebra.Monoid

open import Cat.Displayed.Isofibration
open import Cat.Instances.Sets
open import Cat.Prelude

import Cat.Displayed.Morphism as Dm
import Cat.Morphism as Cm
```
-->

```agda
module Algebra.Monoid.Cat.Isofibration (ℓ : Level) where
```

<!--
```agda
private module Sets = Cm (Sets ℓ)

open Dm (Monoids-on ℓ)

_ = is-category→isofibration

open Monoid-on
open is-monoid-hom
```
-->

# The monoids isofibration {defines="monoids-isofibration"}

Since $\Sets_\kappa$ is a category, $\thecat{Monoids}_\kappa \liesover
\Sets_\kappa$ is `automatically`{.Agda ident=is-category→isofibration}
an [[isofibration]]. For technical reasons it is nonetheless desirable
to have a bespoke but equivalent implementation of this fact, which we
give here.

```agda
private module _ {A B} (e≅ : A Sets.≅ B) (Aᵐ : Monoid-on ⌞ A ⌟) where
  e = iso→equiv e≅
  open Equiv
  module A = Monoid-on Aᵐ
```

Suppose $A$ is a set with the structure of a monoid, and $e : A \simeq
B$ is an equivalence of sets. We define a multiplication on $B$ the same
as for its [[underlying magma|magma isofibration]] and its identity
similarly. That these data satisfy the axioms of a monoid follows by
[[equivalence induction]].

```agda
  Bᵐ : Monoid-on ⌞ B ⌟
  Bᵐ ._⋆_ x y = e .to (e .from x A.⋆ e .from y)
  Bᵐ .identity = e .to A.identity
  Bᵐ .has-is-monoid = EquivJ
    (λ B e → is-monoid (e .to A.identity) (λ x y → e .to (e .from x A.⋆ e .from y)))
    A.has-is-monoid e
```

It is then straightforward to show that both directions of $e$ are
monoid homomorphisms with respect to this structure on $B$.

```agda
  Aᵐ→Bᵐ : is-monoid-hom Aᵐ Bᵐ (e .to)
  Aᵐ→Bᵐ .pres-id = refl
  Aᵐ→Bᵐ .pres-⋆ x y = ap (e .to) $ sym $ ap₂ A._⋆_ (η e x) (η e y)

  Bᵐ→Aᵐ : is-monoid-hom Bᵐ Aᵐ (e .from)
  Bᵐ→Aᵐ .pres-id = η e A.identity
  Bᵐ→Aᵐ .pres-⋆ _ _ = η e _

  Aᵐ≅Bᵐ : Aᵐ ≅[ e≅ ] Bᵐ
  Aᵐ≅Bᵐ = make-iso[ e≅ ] Aᵐ→Bᵐ Bᵐ→Aᵐ prop! prop!

```

Together these give us what we need to show monoids form an isofibration
over sets.

```agda
Monoids-isofibration : Isofibration (Monoids-on ℓ)
Monoids-isofibration = record { _^*_ = Bᵐ ; ^*-lifts = Aᵐ≅Bᵐ }
```

