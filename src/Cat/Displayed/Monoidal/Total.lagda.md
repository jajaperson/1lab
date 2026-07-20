<!--
```agda
open import Cat.Displayed.Functor.Bifunctor.Total
open import Cat.Displayed.Instances.TotalProduct
open import Cat.Displayed.Instances.Functor
open import Cat.Displayed.Functor.Total
open import Cat.Displayed.Monoidal.Base
open import Cat.Functor.Naturality
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Displayed.Morphism.Reasoning as Dr

open Monoidal-category
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
  module Cᵐ = Monoidal-category Cᵐ
  module ℳᵐ = Displayed-monoidal[_] ℳᵐ

  [ℳ,ℳ] = DisCat[ ℳ , ℳ ]
  module [ℳ,ℳ] = Dr [ℳ,ℳ]

  [ℳ³,ℳ] = DisCat[ ℳ ×ᵀᴰ ℳ ×ᵀᴰ ℳ , ℳ ]
  module [ℳ³,ℳ] = Dr [ℳ³,ℳ]
```
-->

```agda
∫ᵐ : Monoidal-category (∫ ℳ)
∫ᵐ .-⊗- = ∫ᵇᶠ ℳᵐ.-⊗'-
∫ᵐ .Unit = ℳᵐ.Unit , ℳᵐ.Unit'
∫ᵐ .unitor-l = ∫ᶠRight'≅Right ℳᵐ.-⊗'-
  ∘ni F-map-iso ∫ᶠⁿ (iso[]→total-iso [ℳ,ℳ] ℳᵐ.unitor-l')
  ∘ni ∫ᶠId'≅Id ni⁻¹
∫ᵐ .unitor-r = ∫ᶠLeft'≅Left ℳᵐ.-⊗'-
  ∘ni F-map-iso ∫ᶠⁿ (iso[]→total-iso [ℳ,ℳ] ℳᵐ.unitor-r')
  ∘ni ∫ᶠId'≅Id ni⁻¹
```
