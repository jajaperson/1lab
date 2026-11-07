<!--
```agda
open import 1Lab.Prelude

open import Algebra.Magma

open import Cat.Displayed.Univalence.Thin

open import Data.Power

import Cat.Displayed.Instances.Subobjects
```
-->

```agda
module Algebra.Magma.Submagma where
```

<!--
```agda
private
  variable
    ℓ : Level
    A B : Magma ℓ

  module _ {ℓ} where open Cat.Displayed.Instances.Subobjects (Magmas ℓ) hiding (to ; from) public
```
-->

# Submagmas

A **submagma** $m$ of a magma $A$ is a [[monomorphism]] $S \xto{m} R$,
that is, an object of the [[poset of subobjects]] $\Sub(G)$.

```agda
Submagma : Magma ℓ → Type (lsuc ℓ)
Submagma = Subobject
```

One can adopt the alternative point of view that a submagma is a
predicate $S : A \to \prop$: We say $S$ _represents_ a submagma if it
is closed under the binary operation.

```agda
represents-submagma : (A : Magma ℓ) (S : ℙ ⌞ A ⌟) → Type ℓ
represents-submagma A S = ∀ {x y} → x ∈ S → y ∈ S → (x ⋆ y) ∈ S where
  open Magma-on (A .snd)
```

If $S$ represents a submagma, then its total space inherits a magma
structure from $A$ so that the first projection $\Sigma S \xto{m} A$ is
a submagma.

```agda
rep-submagma→magma-on
  : (A : Magma ℓ) (S : ℙ ⌞ A ⌟) → represents-submagma A S
  → Magma-on (Σ[ x ∈ A ] x ∈ S)
rep-submagma→magma-on A H sm = let open Magma-on (A .snd) in λ where
    .Magma-on._⋆_ (x , x∈S) (y , y∈S) → (x ⋆ y) , sm x∈S y∈S
    .Magma-on.has-is-magma .is-magma.has-is-set → hlevel 2

predicate→submagma
  : (A : Magma ℓ) (S : ℙ ⌞ A ⌟) → represents-submagma A S
  → Submagma A
predicate→submagma A S sm = record { map = it ; monic = ism } where
  it : Magmas.Hom (el! _ , rep-submagma→magma-on A S sm) A
  it .fst = fst
  it .snd x y = refl

  ism : Magmas.is-monic it
  ism = Homomorphism-monic it λ p → Σ-prop-path! p
```

## Images

If $f : A \to B$ is a magma homomorphism, then its `image`{.Agda} is
naturally viewed as a submagma.

```agda
module _ {A B : Magma ℓ} (f : Magmas.Hom A B) where

  magma-on-image : Magma-on (image (f .fst))
  magma-on-image =
    let module A = Magma-on (A .snd)
        module B = Magma-on (B .snd)
    in λ where
      .Magma-on._⋆_ (x , x∈fA) (y , y∈fA) → (x B.⋆ y) ,
        case x∈fA , y∈fA of λ a fa≡x b fa≡b →
          inc (a A.⋆ b , f .snd a b ∙ ap₂ B._⋆_ fa≡x fa≡b)
      .Magma-on.has-is-magma .is-magma.has-is-set → hlevel 2

  im : Magma ℓ
  im = (el! _) , magma-on-image

  A→im : Magmas.Hom A im
  A→im .fst = image-inc (f .fst)
  A→im .snd x y = Σ-prop-path! (f .snd x y)

  im→B : Magmas.Hom im B
  im→B .fst = fst
  im→B .snd x y = refl

  Im[_] : Submagma B
  Im[_] = record
    { map = im→B
    ; monic = Homomorphism-monic im→B ext
    }
```
