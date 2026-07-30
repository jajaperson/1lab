<!--
```agda
open import Cat.Displayed.Functor.Bifunctor.Total
open import Cat.Displayed.Instances.TotalProduct
open import Cat.Displayed.Instances.Functor
open import Cat.Displayed.Functor.Total
open import Cat.Displayed.Monoidal.Base
open import Cat.Functor.Naturality
open import Cat.Displayed.Functor
open import Cat.Functor.Bifunctor
open import Cat.Monoidal.Functor
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Displayed.Morphism.Reasoning as Dr
import Cat.Reasoning as Cr

open Monoidal-category
open _=[_]=>_
```
-->

```agda
module Cat.Displayed.Monoidal.Total {oc ℓc om ℓm}
  {C : Precategory oc ℓc} {Cᵐ : Monoidal-category C}
  {ℳ : Displayed C om ℓm} (ℳᵐ : Displayed-monoidal[ Cᵐ ] ℳ)
  where
```

## The total monoidal category of a displayed monoidal category {defines=total-monoidal-category}

Unsurprisingly, the [[total category]] $\int \cM$ of a [[displayed
monoidal category]] $\cM \liesover \cC$ is an ordinary [[monoidal
category]].

<!--
```agda
private
  open Cr C
  module C = Monoidal-category Cᵐ
  open Dr ℳ
  open module ℳᵐ = Displayed-monoidal[_] ℳᵐ

```
-->

```agda
∫ᵐ : Monoidal-category (∫ ℳ)
∫ᵐ .-⊗- = ∫ᵇᶠ -⊗'-
∫ᵐ .Unit = ℳᵐ.Unit , Unit'
∫ᵐ .unitor-l = iso→isoⁿ (λ x → iso[]→total-iso ℳ λ≅')
  λ _ → ∫Hom-path _ _ $ symP $ unitor-l'.to' .is-natural' _ _ _
∫ᵐ .unitor-r = iso→isoⁿ (λ x → iso[]→total-iso ℳ ρ≅')
  λ _ →  ∫Hom-path _ _ $ symP $ unitor-r'.to' .is-natural' _ _ _
∫ᵐ .associator = iso→isoⁿ (λ x → iso[]→total-iso ℳ α≅')
  λ _ → ∫Hom-path _ _ $ symP $ associator'.to' .is-natural' _ _ _
∫ᵐ .triangle =  ∫Hom-path _ _ triangle'
∫ᵐ .pentagon = ∫Hom-path _ _ pentagon'
```

The projection `πᶠ`{.Agda} of such a total category carries the
structure of a [[monoidal functor]].

```agda
open Make-monoidal-functor
open Make-binatural-iso

πᶠᵐ : Monoidal-functor-on ∫ᵐ Cᵐ (πᶠ ℳ)
πᶠᵐ = make-monoidal-functor-on $ λ where
  .ε → id-iso
  .F-mult → make-binatural-iso $ λ where
    .eta _ _ → id
    .inv _ _ → id
    .eta∘inv _ _ → id2
    .inv∘eta _ _ → id2
    .is-natural-◀ _ _ → sym id-comm
    .is-natural-▶ _ _ → sym id-comm
  .F-α→ → elimr (idl _ ∙ C.◀.F-id) ∙∙ introl C.▶.F-id ∙∙ sym (idl _)
  .F-λ← → elimr $ idl _ ∙ C.◀.F-id
  .F-ρ← → elimr $ idl _ ∙ C.▶.F-id
```
