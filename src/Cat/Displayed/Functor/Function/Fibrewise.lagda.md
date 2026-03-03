<!--
```agda
open import 1Lab.Function.Fibrewise

open import Cat.Displayed.Reasoning as Dr
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Reasoning as Cr
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.Functor.Function.Fibrewise 
  {oa ℓa oe ℓe ob ℓb of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb} {F : Functor A B}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf} (F' : Displayed-functor F ℰ ℱ)
  where
```

# Displayed functors give functions over

The data `F₀'`{.Agda} and `F₁'`{.Agda} of a [[displayed functor]] are
naturally repackaged as [[functions over|function over]] the 
corresponding data of the base functor.

<!--
```agda
private
  module A = Cr A
  module ℰ = Dr ℰ
  module ℱ = Dr ℱ 

open Functor F
open Displayed-functor F'
```
-->

```agda
F₀-over : ℰ.Ob[_] -[ F₀ ]→ ℱ.Ob[_]
F₀-over a b p a' = subst ℱ.Ob[_] p (F₀' a')

F₁-over 
  : ∀ {x y} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} 
  → (λ f → ℰ.Hom[ f ] x' y') -[ F₁ ]→ λ g → ℱ.Hom[ g ] (F₀' x') (F₀' y')
F₁-over {x' = x'} {y' = y'} f g p f' = ℱ.hom[ p ] (F₁' f')
```

These relate to the original `F₀'`{.Agda} and `F₁'`{.Agda} by the
following paths:

```agda
F₀-over-refl : ∀ x → F₀-over x (F₀ x) refl ≡ F₀'
F₀-over-refl x = funext λ x' → transport-refl (F₀' x')

F₁-over-refl
  : ∀ {x y} (f : A.Hom x y) 
  → ∀ {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} 
  → F₁-over {x' = x'} {y' = y'} f (F₁ f) refl ≡ F₁' {f = f} {a' = x'} {b' = y'}
F₁-over-refl f = funext λ _ → ℱ.liberate refl
```
