
<!--
```agda
open import Algebra.Group.Ab.Cat.Isofibration
open import Algebra.Monoid.Cat.Isofibration
open import Algebra.Group.Ab hiding (module Ab)
open import Algebra.Monoid
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Isofibration
open import Cat.Instances.Sets
open import Cat.Prelude hiding (_+_ ; _*_)

import Cat.Displayed.Morphism as Dm
import Cat.Reasoning as Cr
```
-->

```agda
module Algebra.Ring.Cat.Isofibration (ℓ : Level) where
```

<!--
```agda
private
  module Sets = Cr (Sets ℓ)
  module Mon where
    open Dm (Monoids-on ℓ) public
    open Isofibration (Monoids-isofibration ℓ) public
  module Ab where
    open Dm (Abelian-groups-on ℓ) public
    open Isofibration (Ab-isofibration ℓ) public

open Dm (Rings-on ℓ)

_ = is-category→isofibration

open is-ring-hom
```
-->

# The rings isofibration {defines="ring-isofibration"}

Since $\Sets_\kappa$ is a category, $\Rings_\kappa \liesover
\Sets_\kappa$ is `automatically`{.Agda ident=is-category→isofibration}
an [[isofibration]]. For technical reasons it is nonetheless desirable
to have a bespoke but equivalent implementation of this fact, which we
give here.

```agda
private module _ {A B} (e≅ : A Sets.≅ B) (Aʳ : Ring-on ⌞ A ⌟) where
  e = iso→equiv e≅
  open Equiv
  module A = Ring-on Aʳ
```

Suppose $A$ is a set with the structure of a ring and $e : A \simeq B$
is an equivalence of sets. We can use the [[abelian groups isofibration]]
and the [[monoids isofibration]] to transport the additive group and
multiplicative monoid structures onto $B$, which in turn accounts for
most of the ring structure on $B$.

```agda
  Aᵃ : Abelian-group-on ⌞ A ⌟
  Aᵃ = A.group .snd

  Bᵃ : Abelian-group-on ⌞ B ⌟
  Bᵃ = e≅ Ab.^* Aᵃ

  Aᵐ : Monoid-on ⌞ A ⌟
  Aᵐ = A.multiplicative-monoid .snd

  Bᵐ : Monoid-on ⌞ B ⌟
  Bᵐ = e≅ Mon.^* Aᵐ

  module B where
    open Abelian-group-on Bᵃ using (has-is-ab) renaming (_*_ to _+_) public
    open Monoid-on Bᵐ using (has-is-monoid) renaming (identity to 1r ; _⋆_ to _*_) public

  Bʳ : Ring-on ⌞ B ⌟
  Bʳ = λ where
    .Ring-on.1r  → B.1r
    .Ring-on._+_ → B._+_
    .Ring-on._*_ → B._*_
    .Ring-on.has-is-ring → λ where
      .is-ring.+-group → B.has-is-ab
      .is-ring.*-monoid → B.has-is-monoid
```

The slightly fiddly part is showing distributivity, which we can do by
[[equivalence induction]].

```agda
      .is-ring.*-distribl {x} {y} {z} → EquivJ
        (λ B e → ∀ {x y z} →
          e .to (x A.* e .from (e .to (y A.+ z))) ≡
          e .to (e .from (e .fst (x A.* y)) A.+ e .from (e .fst (x A.* z))))
        A.*-distribl e
      .is-ring.*-distribr {x} {y} {z} → EquivJ
        (λ B e → ∀ {x y z} →
          e .to (e .from (e .to (y A.+ z)) A.* x) ≡
          e .to (e .from (e .fst (y A.* x)) A.+ e .from (e .fst (z A.* x))))
        A.*-distribr e
```

Similarly, we can use the lifts of $e$ to group and monoid isomorphisms
in order to show that $e$ is a ring homomorphism.

```agda
  Aᵃ≅Bᵃ : Aᵃ Ab.≅[ e≅ ] Bᵃ
  Aᵃ≅Bᵃ = Ab.^*-lifts e≅ Aᵃ

  Aᵐ≅Bᵐ : Aᵐ Mon.≅[ e≅ ] Bᵐ
  Aᵐ≅Bᵐ = Mon.^*-lifts e≅ Aᵐ
  
  module e where
    open Equiv e public
    module a = Ab._≅[_]_ Aᵃ≅Bᵃ
    module m = Mon._≅[_]_ Aᵐ≅Bᵐ

  Aʳ→Bʳ : is-ring-hom Aʳ Bʳ e.to
  Aʳ→Bʳ .pres-id = e.m.to' .is-monoid-hom.pres-id
  Aʳ→Bʳ .pres-*  = e.m.to' .is-monoid-hom.pres-⋆
  Aʳ→Bʳ .pres-+  = e.a.to' .is-group-hom.pres-⋆
  
  Bʳ→Aʳ : is-ring-hom Bʳ Aʳ e.from
  Bʳ→Aʳ .pres-id = e.m.from' .is-monoid-hom.pres-id
  Bʳ→Aʳ .pres-*  = e.m.from' .is-monoid-hom.pres-⋆
  Bʳ→Aʳ .pres-+  = e.a.from' .is-group-hom.pres-⋆

  Aʳ≅Bʳ : Aʳ ≅[ e≅ ] Bʳ
  Aʳ≅Bʳ = make-iso[ e≅ ] Aʳ→Bʳ Bʳ→Aʳ prop! prop!
```

Together these give us exactly what we need to show rings form an
isofibration over sets.

```agda
Rings-isofibration : Isofibration (Rings-on ℓ)
Rings-isofibration = record { _^*_ = Bʳ ; ^*-lifts = Aʳ≅Bʳ }
```

