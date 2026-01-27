<!--
```agda
open import Cat.Displayed.Functor.Properties
open import Cat.Displayed.Functor.Total
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as Dr
import Cat.Displayed.Morphism as Dm
import Cat.Displayed.Morphism.Total as Tm
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Functor.Properties.Total
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B} {F' : Displayed-functor F ℰ ℱ}
  where
```

<!--
```agda
private
  module ℰ where 
    open Dr ℰ public
    open Dm ℰ public
  module ℱ where
    open Dr ℱ public
    open Dm ℱ public
    open Tm ℱ public
  module ∫ℰ = Cr (∫ ℰ)
  module ∫ℱ = Cr (∫ ℱ)
  ∫F' = ∫ᶠ F'

open Functor
open Displayed-functor
```
-->

# Properties of total functors

In this module we show how properties of a [[displayed functor]] relate
to properties of its [[total functor]].


Total-essential-fibre : Displayed-functor F ℰ ℱ → ∀ {b} (b' : ℱ.Ob[ b ]) → Type _
Total-essential-fibre {F = F} F' {b} b' = 
  Σ (Essential-fibre F b) λ (a , f) → Σ ℰ.Ob[ a ] λ a' → ₀' F' a' ℱ.≅[ f ] b'


This leads to the following generalization of essential surjectivity on
objects:


is-total-split-eso : Displayed-functor F ℰ ℱ → Type _
is-total-split-eso F' = ∀ {b} b' → Total-essential-fibre F' {b} b'

is-total-eso : Displayed-functor F ℰ ℱ → Type _
is-total-eso F' = ∀ {b} b' → ∥ Total-essential-fibre F' {b}  b' ∥


Note that this does _not_ imply essential surjectivity on objects for 
the base functor, since the displayed categories may not display objects
over objects in every isomorphism class in the base category.

Total-essential-fibre-≃ 
  : ∀ {b} (b' : ℱ.Ob[ b ]) → Total-essential-fibre F' b' ≃ Essential-fibre ∫F' (b , b')
Total-essential-fibre-≃ {b} b' = Iso→Equiv (tef→ , iso tef← rinv linv) where
  tef→ : Total-essential-fibre F' b' → Essential-fibre ∫F' (b , b')
  tef→ ((a , Fa≅b) , a' , Fa'≅b') = (a , a') , ℱ.∫≅ Fa'≅b'

  tef← : Essential-fibre ∫F' (b , b') → Total-essential-fibre F' b'
  tef← ((a , a') , ∫f) = (a , ℱ.D≅ ∫f .fst) , a' , ℱ.D≅ ∫f .snd

  rinv : is-right-inverse tef← tef→
  rinv ((a , a') , ∫f) = Σ-path refl (transport-refl _)

  linv : is-left-inverse tef← tef→
  linv ((a , f) , a' , f') = Σ-path refl (Σ-path (transport-refl _) {! pa  !})
