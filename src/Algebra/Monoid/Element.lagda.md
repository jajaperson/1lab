<!--
```agda
open import Algebra.Monoid

open import Cat.Instances.Delooping
open import Cat.Prelude

import Algebra.Monoid.Reasoning as Kit

import Cat.Morphism as Cm
```
-->


```agda
module Algebra.Monoid.Element {ℓ} {(M , Mᴹ) : Monoid ℓ} where
```

# Elements of monoids

In this module we define certain properties elements of a monoid $M$
might have. Since $M$ as a [[category]], namely its [[delooping
category]] $\B{M}$, a bunch of these come directly from corresponding
properties of [morphisms].

[morphisms]: Cat.Morphism.html

<details>
<summary>We are renaming and exporting _a lot_, so we have hidden it in
this `<details>` tag.
</summary>

```agda
open Monoid-on Mᴹ using () renaming (identity to 1m)

open Cm (B Mᴹ) using
    ( is-invertible ; is-invertible-inverse ; is-invertible-is-prop
    ; Inverses ; Inverses-are-prop ; Inverses-∘ ; invertible-∘ ; _invertible⁻¹
    ; make-inverses ; make-invertible ; inverses→invertible
    ; inverses-cancell ; inverses-cancelr ; invertible-cancell ; invertible-cancelr
    ; is-monic ; is-monic-is-prop ; invertible→monic
    ; is-epic ; is-epic-is-prop ; invertible→epic
    ; monic-cancell ; epic-cancelr
    ; _section-of_ ; section-of-is-prop ; has-section ; make-section
    ; section-cancell ; has-section→epic
    ; _retract-of_ ; retract-of-is-prop ; has-retract ; make-retract
    ; retract-cancelr ; has-retract→monic
    ; section-of+epic→retract-of ; retract-of+monic→section-of
    ; inverses→to-has-section ; inverses→from-has-section
    ; inverses→to-has-retract ; inverses→from-has-retract
    ; invertible→to-has-section ; invertible→from-has-section
    ; invertible→to-has-retract ; invertible→from-has-retract
    ; retract-of+monic→inverses ; section-of+epic→inverses
    ; is-split-monic ; is-split-epic ; split-epic→epic ; split-monic→mono
    ; to ; from
    )
  renaming
    ( id-monic to 1-monic ; id-epic to 1-epic
    ; ∘-is-monic to *-is-monic ; ∘-is-epic to *-is-epic
    ; monic-postcomp-embedding to monic-postmult-embedding
    ; epic-precomp-embedding to epic-premult-embedding
    ; id-has-section to 1-has-section ; section-of-∘ to section-of-* ; section-∘ to section-*
    ; id-has-retract to 1-has-retract ; retract-of-∘ to retract-of-* ; retract-∘ to retract-*
    ; id-invertible to 1-invertible ; id-iso to 1-unit ; _∘Iso_ to _*Unit_
    ; _Iso⁻¹ to _Unit⁻¹ ; make-iso to make-unit ; make-iso! to make-unit!
    ; involution→iso to involution→unit ; invertible→iso to invertible→unit
    ; iso→invertible to unit→invertible ; inverse-unique₀ to inverse-unique
    ; iso→to-has-section to unit→to-has-section
    ; iso→from-has-section to unit→from-has-section
    ; iso→to-has-retract to unit→to-has-retract
    ; iso→from-has-retract to unit→from-has-retract
    ; iso→monic to unit→monic ; iso→epic to unit→epic
    ; module _≅_ to Unit
    )
  public
```

</details>

A **cancellable** element is both monic and epic, as morphisms of the
delooping.

```agda
is-cancellable : M → Type ℓ
is-cancellable x = is-monic x × is-epic x

is-cancellable-is-prop : ∀ x → is-prop (is-cancellable x)
is-cancellable-is-prop x = ×-is-hlevel 1 (is-monic-is-prop x) (is-epic-is-prop x)

1-cancellable : is-cancellable 1m
1-cancellable = 1-monic , 1-epic

invertible→cancellable : ∀ {x} → is-invertible x → is-cancellable x
invertible→cancellable inv = invertible→monic inv , invertible→epic inv
```

An invertible element is also called a **unit**[^1]

[^1]: Not to be confused with the unit of an adjunction)

```agda
Unit = Cm.Isomorphism (B Mᴹ) tt tt

unit→regular : (x : Unit) → is-cancellable (x .to)
unit→regular u = unit→monic u , unit→epic u
```
