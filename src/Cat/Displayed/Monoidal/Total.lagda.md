<!--
```agda
open import Cat.Displayed.Functor.Bifunctor.Total
open import Cat.Displayed.Instances.TotalProduct
open import Cat.Displayed.Instances.Functor
open import Cat.Displayed.Functor.Total
open import Cat.Displayed.Monoidal.Base
open import Cat.Functor.Naturality
open import Cat.Displayed.Functor
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Displayed.Morphism.Reasoning as Dr

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
  open Precategory C
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
