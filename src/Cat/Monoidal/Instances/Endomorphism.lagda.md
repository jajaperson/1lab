<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Monoidal.Base
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Reasoning as Cr

open _=>_
```
-->

```agda
module Cat.Monoidal.Instances.Endomorphism where
```

# Endomorphism categories {defines="endomorphism-category"}

In the same way that, if you have a category $\cC$, making a choice
of object $a : \cC$ canonically gives you a monoid
$\rm{Endo}_\cC(a)$ of _endomorphisms_ $a \to a$, having a [[bicategory]]
$\bicat{B}$ and choosing an object $a : \bicat{B}$ canonically gives you
a choice of _[[monoidal category]]_, $\rm{Endo}_\bicat{B}(a)$.

```agda
Endomorphisms
  : ∀ {o ℓ ℓ'} (B : Prebicategory o ℓ ℓ')
  → (a : Prebicategory.Ob B)
  → Monoidal-category (Prebicategory.Hom B a a)
Endomorphisms B a = mon where
  open Monoidal-category
  module B = Prebicategory B
  mon : Monoidal-category (B.Hom a a)
  mon .-⊗- = B.compose
  mon .Unit = B.id
  mon .unitor-l = B.unitor-l
  mon .unitor-r = B.unitor-r
  mon .associator = to-natural-iso $ ni where
    open make-natural-iso
    open Cr
    ni : make-natural-iso _ _
    ni .eta _ = B.α→ _
    ni .inv _ = B.α← _
    ni .eta∘inv _ = Cr.invl _ B.associator ηₚ _
    ni .inv∘eta _ = Cr.invr _ B.associator ηₚ _
    ni .natural x y f = sym $ Cr.to B.associator .is-natural _ _ _
  mon .triangle = B.triangle _ _
  mon .pentagon = B.pentagon _ _ _ _
```

In the opposite direction, the [delooping] of a monoidal category gives
a bicategory.

[delooping]: Cat.Bi.Instances.Delooping.html
