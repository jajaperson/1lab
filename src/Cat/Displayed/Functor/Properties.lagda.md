<!--
```agda
open import Cat.Displayed.Reasoning as Dr
open import Cat.Displayed.Morphism as Dm
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Functor.Properties 
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  where
```

<!--
```agda
private
  module A = Cr A
  module ℰ where 
    open Dr ℰ public
    open Dm ℰ public
  module ℱ where
    open Dr ℱ public
    open Dm ℱ public
  variable
    F : Functor A B

open Functor
open Displayed-functor
```
-->

# Properties of displayed functors

This module mirrors the corresponding one for [ordinary functors]
by defining the corresponding classes of [[displayed functors|displayed functor]].
Suppose $F : \cA \to \cB$ is a functor and $F' : \cE \to_F \cF$ is a 
displayed functor over $F$.

```agda
module _ {F} (F' : Displayed-functor F ℰ ℱ) where
```

[ordinary functors]: Cat.Functor.Properties.html

:::{.definition #fully-displayed-functor}
$F'$ is **fully displayed** when its action on hom-sets _over_ any 
morphism is surjective:

```agda
  is-full[] : Type _
  is-full[] = 
    ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]}
    → is-surjective {A = ℰ.Hom[ f ] x' y'} (₁' F')
```
:::

:::{.definition #faithfully-displayed-functor}
$F : \cE$ functor is **faithfully displayed** when its action on hom-sets
_over_ any morphism is injective. The obvious way to write this up is

```agda
  is-fibrewise-injective : Type _
  is-fibrewise-injective = 
    ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]}
    → injective {A = ℰ.Hom[ f ] x' y'} (₁' F')
```

this form is inconvenient to use, since two displayed morphisms being
compared need definitionally equal base morphisms. Hence we reserve 
`is-faithful[]`{.Agda} for a more useful, but logically equivalent form:

```agda
  is-faithful[] : Type _
  is-faithful[] = 
    ∀ {x y f g} {f=g : f ≡ g}
      {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} 
      {f' : ℰ.Hom[ f ] x' y'} {g' : ℰ.Hom[ g ] x' y'}
    → ₁' F' f' ℱ.≡[ ap (₁ F) f=g ] ₁' F' g'
    → f' ℰ.≡[ f=g ] g'

  fibrewise-injective→faithful[] : is-fibrewise-injective → is-faithful[]
  fibrewise-injective→faithful[] inj' {x} {y} {f} {g} {f=g} = 
    J (λ h f=h → 
        ∀ {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]}
          {f' : ℰ.Hom[ f ] x' y'} {h' : ℰ.Hom[ h ] x' y'} 
        → ₁' F' f' ℱ.≡[ ap (₁ F) f=h ] ₁' F' h' 
        → f' ℰ.≡[ f=h ] h') 
      inj' f=g
  
  faithful[]→fibrewise-injective[] : is-faithful[] → is-fibrewise-injective
  faithful[]→fibrewise-injective[] faith' = faith'
```
:::

## Fully faithfully displayed functors {defines="fully-faithfully-displayed-functor fully-faithfully-displayed"}

A displayed functor is **fully faithfully displayed** when its action on
hom-sets _over_ any morphism is an equivalence.

```agda
  is-ff[] : Type _
  is-ff[] = ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} 
    →  is-equiv {A = ℰ.Hom[ f ] x' y'} (₁' F')

  ff[]→faithful[] : is-ff[] → is-faithful[]
  ff[]→faithful[] ff' = 
    fibrewise-injective→faithful[] (Equiv.injective (₁' F' , ff'))

  ff[]→full[] : is-ff[] → is-full[]
  ff[]→full[] ff' f' = inc (equiv→inverse ff' f' , equiv→counit ff' f')

  full[]+faithful[]→ff[] : is-full[] → is-faithful[] → is-ff[]
  full[]+faithful[]→ff[] full' faith' .is-eqv = p where
    img-is-prop : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} f'
      → is-prop (fibre {A = ℰ.Hom[ f ] x' y'} (₁' F') f')
    img-is-prop f' (g' , p) (h' , q) = Σ-prop-path 
      (λ x → ℱ.Hom[ ₁ F _ ]-set (₀' F' _) (₀' F' _) (₁' F' x) f') 
      (faith' (p ∙ sym q))

    p : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} f' 
      → is-contr (fibre {A = ℰ.Hom[ f ] x' y'} (₁' F') f')
    p f' .centre = ∥-∥-elim (λ _ → img-is-prop f') (λ x → x) (full' f')
    p f' .paths = img-is-prop f' _
```

A fully faithfully functor over a fully faithful functor gives an 
[[equivalence over]] between displayed hom-sets:

```agda
  ff[ff]→equiv-over
      : ∀ (ff : is-fully-faithful F) (ff' : is-ff[])
      → ∀ {x y} (x' : ℰ.Ob[ x ]) (y' : ℰ.Ob[ y ])
      → (λ f → ℰ.Hom[ f ] x' y') ≃[ ₁ F , ff ] λ f → ℱ.Hom[ f ] (₀' F' x') (₀' F' y')
  ff[ff]→equiv-over ff ff' {x = x} {y = y} x' y' f g Ff=g = Iso→Equiv 
    (to , (iso from rinv linv))
    where
      module ff' = Equiv (₁' F' {x} {y} {f} {x'} {y'}, ff')
      
      to : ℰ.Hom[ f ] x' y' → ℱ.Hom[ g ] (₀' F' x') (₀' F' y')
      to f' = ℱ.hom[ Ff=g ] (₁' F' f')

      from : ℱ.Hom[ g ] (₀' F' x') (₀' F' y') → ℰ.Hom[ f ] x' y'
      from = λ g' → ff'.from (ℱ.hom[ Ff=g ]⁻ g')

      rinv : is-right-inverse from to
      rinv g' = 
        ℱ.hom[ Ff=g ] ⌜ ₁' F' (ff'.from (ℱ.hom[ Ff=g ]⁻ g')) ⌝ ≡⟨ ap! (ff'.ε _) ⟩ 
        ℱ.hom[ Ff=g ] (ℱ.hom[ Ff=g ]⁻ g')                      ≡˘⟨ ℱ.coh[ refl ] _ ∙ ℱ.duplicate _ _ _ ⟩
        g'                                                     ∎

      linv : is-left-inverse from to
      linv f' =
        ff'.from ⌜ ℱ.hom[ Ff=g ]⁻ (ℱ.hom[ Ff=g ] (₁' F' f')) ⌝ ≡˘⟨ ap¡ (ℱ.coh[ refl ] _ ∙ ℱ.duplicate _ _ _) ⟩
        ff'.from (₁' F' f')                                    ≡⟨ ff'.η _ ⟩
        f'                                                     ∎
```

## Essential fibres {defines="essentially-split-surjective-over"}

One way to generalize [[essential fibres|essential fibre]] is as 
follows:

```agda
Essential-fibre[_] 
  : ∀ {b} ((a , f) : Essential-fibre F b) → Displayed-functor F ℰ ℱ 
  → ℱ.Ob[ b ] → Type _
Essential-fibre[_] {b = b} (a , f) F' b' = Σ ℰ.Ob[ a ] λ a' → ₀' F' a' ℱ.≅[ f ] b'

is-split-eso[_] : is-split-eso F → Displayed-functor F ℰ ℱ → Type _
is-split-eso[ eso ] F' = ∀ {b} b' → Essential-fibre[ eso b ] F' b'
```
