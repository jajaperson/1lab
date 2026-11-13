<!--
```agda
open import Algebra.Monoid

open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude

open import Data.Power

import Cat.Displayed.Instances.Subobjects
```
-->

```agda
module Algebra.Monoid.Submonoid where
```

<!--
```agda
private
  variable
    ℓ : Level
    A B : Monoid ℓ

  module _ {ℓ} where open Cat.Displayed.Instances.Subobjects (Monoids ℓ) hiding (to ; from) public
```
-->

# Submonoids

A **submonoid** $m$ of a monoid $M$ is a [[monomorphism]] $S \xto{m} M$,
that is, an object of the [[poset of subobjects]] $\Sub(G)$.

```agda
Submonoid : Monoid ℓ → Type (lsuc ℓ)
Submonoid = Subobject
```

Just as with [[submagmas]], one can adopt the alternative point of view
that a submagma is a special kind of predicate $S : A \to \prop$: We say
$S$ _represents_ a submonoid if it is closed under the binary operation
and contains the identity.

```agda
record represents-submonoid (M : Monoid ℓ) (S : ℙ ⌞ M ⌟) : Type ℓ where
  open Monoid-on (M .snd)
  field
    has-id : identity ∈ S
    has-⋆ : ∀ {x y} → x ∈ S → y ∈ S → (x ⋆ y) ∈ S
```

If $S$ represents a submonoid, then its total space inherits a monoid
structure from $M$ so that the first projection $\int_p S \xto{m} M$ is
a monoid homomorphism.

```agda
rep-submonoid→monoid-on
  : {M : Monoid ℓ} (S : ℙ ⌞ M ⌟) → represents-submonoid M S
  → Monoid-on (∫ₚ S)
rep-submonoid→monoid-on {M = M} S sm =
  let open Monoid-on (M .snd)
      open represents-submonoid sm
  in to-monoid-on λ where
    .make-monoid.monoid-is-set → hlevel 2
    .make-monoid._⋆_ (x , x∈S) (y , y∈S) → x ⋆ y , has-⋆ x∈S y∈S
    .make-monoid.1M → identity , has-id
    .make-monoid.⋆-assoc x y z → Σ-prop-path! associative
    .make-monoid.⋆-idl x → Σ-prop-path! idl
    .make-monoid.⋆-idr x → Σ-prop-path! idr

predicate→submonoid
  : {M : Monoid ℓ} (S : ℙ ⌞ M ⌟) → represents-submonoid M S
  → Submonoid M
predicate→submonoid {M = M} S sm = record { map = it ; monic = ism } where
  it : Monoids.Hom (el! _ , (rep-submonoid→monoid-on S sm)) M
  it .fst = fst
  it .snd .is-monoid-hom.pres-⋆ _ _ = refl
  it .snd .is-monoid-hom.pres-id = refl

  ism : Monoids.is-monic it
  ism = Homomorphism-monic it Σ-prop-path!
```
