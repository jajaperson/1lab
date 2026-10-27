<!--
```agda
open import Algebra.Monoid

open import Cat.Instances.Delooping
open import Cat.Prelude hiding (_*_)

import Algebra.Monoid.Reasoning as Kit

import Cat.Morphism as Cm
```
-->


```agda
module Algebra.Monoid.Element {ℓ} {(M , Mᴹ) : Monoid ℓ} where
```

# Elements of monoids

<!--
```agda
open Monoid-on Mᴹ renaming (_⋆_ to _*_)

private variable
  x y : M
```
-->

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
    ; Inverses ; Inverses-are-prop ; _invertible⁻¹
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
    ; is-cancellable ; is-cancellable-is-prop ; invertible→cancellable
    ; to ; from ; retract ; is-retract ; section ; is-section
    )
  renaming
    ( id-monic to 1-monic ; id-epic to 1-epic
    ; ∘-is-monic to *-is-monic ; ∘-is-epic to *-is-epic
    ; monic-postcomp-embedding to monic-postmult-embedding
    ; epic-precomp-embedding to epic-premult-embedding
    ; id-has-section to 1-has-section ; section-of-∘ to section-of-* ; section-∘ to section-*
    ; id-has-retract to 1-has-retract ; retract-of-∘ to retract-of-* ; retract-∘ to retract-*
    ; id-invertible to 1-invertible ; id-iso to 1-unit
    ; invertible-∘ to invertible-* ; Inverses-∘ to Inverses-* ; _∘Iso_ to _*Unit_
    ; _Iso⁻¹ to _Unit⁻¹ ; make-iso to make-unit ; make-iso! to make-unit!
    ; involution→iso to involution→unit ; invertible→iso to invertible→unit
    ; iso→invertible to unit→invertible ; inverse-unique₀ to inverse-unique
    ; iso→to-has-section to unit→to-has-section
    ; iso→from-has-section to unit→from-has-section
    ; iso→to-has-retract to unit→to-has-retract
    ; iso→from-has-retract to unit→from-has-retract
    ; iso→monic to unit→monic ; iso→epic to unit→epic
    ; id-cancellable to 1-cancellable ; ∘-cancellable to *-cancellable
    ; iso→cancellable to unit→cancellable
    ; module _≅_ to Unit
    )
  public
```

</details>

An invertible element is also called a **unit**.[^1]

[^1]: Not to be confused with the unit of an adjunction)

```agda
Unit = Cm.Isomorphism (B Mᴹ) tt tt
```

## Elements of commutative monoids

We also define helpers for when $M$ is commutative.

```agda
module Commutative (*-commutes : ∀ {x y} → x * y ≡ y * x) where

  monic→cancellable : is-monic x → is-cancellable x
  monic→cancellable xᵐ .fst = xᵐ
  monic→cancellable xᵐ .snd a b p = xᵐ a b
    (*-commutes ∙∙ p ∙∙ *-commutes)
  
  epic→cancellable : is-epic x → is-cancellable x
  epic→cancellable xᵉ .fst a b p = xᵉ a b
    (sym *-commutes ∙∙ p ∙∙ sym *-commutes)
  epic→cancellable xᵉ .snd = xᵉ

  has-retract→invertible : has-retract x → is-invertible x
  has-retract→invertible (make-retract x⁻¹ linv) =
    make-invertible x⁻¹ (*-commutes ∙ linv) linv

  has-section→invertible : has-section x → is-invertible x
  has-section→invertible (make-section x⁻¹ rinv) =
    make-invertible x⁻¹ rinv (sym *-commutes ∙ rinv)
```
