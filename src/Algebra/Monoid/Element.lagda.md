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
    ; to ; from
    )
  renaming
    ( is-monic to is-lregular ; is-monic-is-prop to is-lregular-is-prop
    ; invertible→monic to invertible→lregular
    ; is-epic to is-rregular ; is-epic-is-prop to is-rregular-is-prop
    ; invertible→epic to invertible→rregular
    ; id-monic to 1-lregular ; id-epic to 1-rregular
    ; ∘-is-monic to *-is-lregular ; ∘-is-epic to *-is-rregular
    ; monic-cancell to lregular-cancell ; epic-cancelr to rregular-cancelr
    ; monic-postcomp-embedding to lregular-postmult-embedding
    ; epic-precomp-embedding to rregular-premult-embedding
    ; _section-of_ to _rinv-of_ ; section-of-is-prop to rinv-of-is-prop
    ; has-section to has-rinv ; make-section to make-rinv
    ; id-has-section to 1-has-rinv ; section-of-∘ to rinv-of-* ; section-∘ to rinv-*
    ; section-cancell to rinv-cancell ; has-section→epic to has-rinv→rregular
    ; _retract-of_ to _linv-of_ ; retract-of-is-prop to linv-of-is-prop
    ; has-retract to has-linv ; make-retract to make-linv
    ; id-has-retract to 1-has-retract ; retract-of-∘ to linv-of-* ; retract-∘ to linv-*
    ; retract-cancelr to linv-cancelr ; has-retract→monic to has-linv→lregular
    ; section-of+epic→retract-of to rinv-of+rregular→linv-of
    ; retract-of+monic→section-of to linv-of+lregular→rinv-of
    ; id-invertible to 1-invertible
    ; id-iso to 1-unit ; _∘Iso_ to _*Unit_
    ; _Iso⁻¹ to _Unit⁻¹ ; make-iso to make-unit ; make-iso! to make-unit!
    ; involution→iso to involution→unit ; invertible→iso to invertible→unit
    ; iso→invertible to unit→invertible ; inverse-unique₀ to inverse-unique
    ; iso→monic to unit→lregular ; iso→epic to unit→rregular
    ; inverses→to-has-section to inverses→to-has-rinv
    ; inverses→from-has-section to inverses→from-has-rinv
    ; inverses→to-has-retract to inverses→to-has-linv
    ; inverses→from-has-retract to inverses→from-has-linv
    ; invertible→to-has-section to invertible→to-has-rinv
    ; invertible→from-has-section to invertible→from-has-rinv
    ; invertible→to-has-retract to invertible→to-has-linv
    ; invertible→from-has-retract to invertible→from-has-linv
    ; iso→to-has-section to unit→to-has-rinv
    ; iso→from-has-section to unit→from-has-rinv
    ; iso→to-has-retract to unit→to-has-linv
    ; iso→from-has-retract to unit→from-has-linv
    ; retract-of+monic→inverses to linv-of+lregular→inverses
    ; section-of+epic→inverses to rinv-of+rregular→inverses
    ; is-split-monic to is-lunit ; is-split-epic to is-runit
    ; split-epic→epic to runit→rregular ; split-monic→mono to lunit→lregular
    ; module _≅_ to Unit
    )
  public
```

</details>

An element which is cancellable on the left is called **left regular**,
while one which is cancellable on the right is called **right regular**.
A **regular** element is both left- and right-regular.

```agda
is-regular : M → Type ℓ
is-regular x = is-lregular x × is-rregular x

is-regular-is-prop : ∀ x → is-prop (is-regular x)
is-regular-is-prop x = ×-is-hlevel 1 (is-lregular-is-prop x) (is-rregular-is-prop x)

1-regular : is-regular 1m
1-regular = 1-lregular , 1-rregular

invertible→regular : ∀ {x} → is-invertible x → is-regular x
invertible→regular inv = invertible→lregular inv , invertible→rregular inv
```

An invertible element is also called a **unit**[^1]

[^1]: Not to be confused with the unit of an adjunction)

```agda
Unit = Cm.Isomorphism (B Mᴹ) tt tt

unit→regular : (x : Unit) → is-regular (x .to)
unit→regular u = unit→lregular u , unit→rregular u
```
