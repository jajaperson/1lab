<!--
```agda
open import Algebra.Magma

open import Cat.Displayed.Isofibration
open import Cat.Instances.Sets
open import Cat.Prelude

import Cat.Displayed.Morphism as Dm
import Cat.Reasoning as Cr
```
-->

```agda
module Algebra.Magma.Cat.Isofibration (ℓ : Level) where
```

<!--
```agda
private module Sets = Cr (Sets ℓ)

open Dm (Magmas-on ℓ)

_ = is-category→isofibration

open Magma-on
open is-magma
```
-->

# The magmas isofibration {defines="magma-isofibration"}

Since $\Sets_\kappa$ is a category, $\thecat{Magmas}_\kappa \liesover
\Sets_\kappa$ is `automatically`{.Agda ident=is-category→isofibration}
an [[isofibration]]. For technical reasons it is nonetheless desirable
to have a bespoke but equivalent implementation of this fact, which we
give here.

```agda
private module _ {A B} (e≅ : A Sets.≅ B) (Aᵐ : Magma-on ⌞ A ⌟) where
  open Equiv (iso→equiv e≅)
  module A = Magma-on Aᵐ
```

Suppose $A$ is a set with the structure of a magma, and $e : A \simeq
B$ is an equivalence of sets. We define the multiplication of $x,y : B$
by taking the elements to $A$, multiplying them, and then mapping the
result back to $B$.

```agda
  Bᵐ : Magma-on ⌞ B ⌟
  Bᵐ ._⋆_ x y = to (from x A.⋆ from y)
  Bᵐ .has-is-magma .has-is-set = hlevel 2
```

With this structure, both directions of $e$ become magma homomorphisms.

```agda
  Aᵐ→Bᵐ : is-magma-hom Aᵐ Bᵐ to
  Aᵐ→Bᵐ x y = ap to $ sym $ ap₂ A._⋆_ (η x) (η y)

  Bᵐ→Aᵐ : is-magma-hom Bᵐ Aᵐ from
  Bᵐ→Aᵐ _ _ = η _

  e' : Aᵐ ≅[ e≅ ] Bᵐ
  e' = make-iso[ e≅ ] Aᵐ→Bᵐ Bᵐ→Aᵐ prop! prop!
```

Together these give us what we need to show magmas form an isofibration
over sets.

```agda
Magmas-isofibration : Isofibration (Magmas-on ℓ)
Magmas-isofibration = record { _^*_ = Bᵐ ; ^*-lifts = e' }
```
