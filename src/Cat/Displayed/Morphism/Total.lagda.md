<!--
```agda
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Morphism as Dm
import Cat.Displayed.Reasoning as Dr
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Morphism.Total 
  {oa ℓa oe ℓe} {A : Precategory oa ℓa} (ℰ : Displayed A oe ℓe)
  where
```

<!--
```agda
open Dr ℰ
open Dm ℰ
open Cr A

private
  module ∫ = Cr (∫ ℰ)
```
-->

# Morphisms in total categories

This module shows how properties of [displayed morphisms] induce
corresponding properties of morphisms in the [[total category]].

[displayed morphisms]: Cat.Displayed.Morphism.html

## Isos

A [[displayed isomorphism]] gives an [[isomorphism]] in the total
category.

```agda
∫Inverses
  : ∀ {x y x' y'} {f : Hom x y} {g : Hom y x}
    {f' : Hom[ f ] x' y'} {g' : Hom[ g ] y' x'}
    {inv : Inverses f g}
  → Inverses[ inv ] f' g'
  → ∫.Inverses (∫hom f f') (∫hom g g')
∫Inverses {inv = inv} inv' = record 
  { invl = ∫Hom-path ℰ (inv .Inverses.invl) (inv' .Inverses[_].invl') 
  ; invr = ∫Hom-path ℰ (inv .Inverses.invr) (inv' .Inverses[_].invr') }

∫is-invertible
  : ∀ {x y x' y'} {f : Hom x y}
    {f' : Hom[ f ] x' y'}
    {f-inv : is-invertible f}
  → is-invertible[ f-inv ] f'
  → ∫.is-invertible (∫hom f f')
∫is-invertible {f-inv = f-inv} f'-inv = record 
  { inv = ∫hom (f-inv .is-invertible.inv) (f'-inv .is-invertible[_].inv') 
  ; inverses = ∫Inverses (f'-inv .is-invertible[_].inverses') }

∫≅
  : ∀ {x y} {x' : Ob[ x ]} {y' : Ob[ y ]}
    {x≅y : x ≅ y}
  → x' ≅[ x≅y ] y'
  → (x , x') ∫.≅ (y , y')
∫≅ {x≅y = x≅y} x'≅y' = record 
  { to = ∫hom (x≅y ._≅_.to) (x'≅y' ._≅[_]_.to') 
  ; from = ∫hom (x≅y ._≅_.from) (x'≅y' ._≅[_]_.from') 
  ; inverses = ∫Inverses (x'≅y' .inverses') }
```

In fact, isomorphisms in the total category all correspond to
displayed isomorphisms. Here we show the uncurried versions of the above
functions give rise to isomorphisms of types:

```
∫Inverses-iso
  : ∀ {x y x' y'} {f : Hom x y} {g : Hom y x}
    {f' : Hom[ f ] x' y'} {g' : Hom[ g ] y' x'}
  → Iso (Σ (Inverses f g) (λ inv → Inverses[ inv ] f' g'))
        (∫.Inverses (∫hom f f') (∫hom g g'))

∫is-invertible-iso
  : ∀ {x y x' y'} {f : Hom x y} {f' : Hom[ f ] x' y'}
  → Iso (Σ (is-invertible f) (λ f-inv → is-invertible[ f-inv ] f'))
        (∫.is-invertible (∫hom f f'))

∫≅-iso
  : ∀ {x y} {x' : Ob[ x ]} {y' : Ob[ y ]}
  → Iso (Σ (x ≅ y) (λ x≅y → x' ≅[ x≅y ] y')) ((x , x') ∫.≅ (y , y'))
```

<details>
<summary>Construction of equivalences `∫Inverses-equiv`{.Agda},
`∫is-invertible-equiv`{.Agda}, and `∫≅-equiv`{.Agda}.</summary>
```agda
DInverses
  : ∀ {x y x' y'} 
    {∫f : ∫.Hom (x , x') (y , y')} {∫g : ∫.Hom (y , y') (x , x')}
  → ∫.Inverses (∫f) (∫g)
  → Σ (Inverses (∫f .∫Hom.fst) (∫g .∫Hom.fst)) λ inv 
    → Inverses[ inv ] (∫f .∫Hom.snd) (∫g .∫Hom.snd)
DInverses {∫f = ∫hom f f'} {∫g = ∫hom g g'} ∫inv = inv , inv' where
  module ∫inv = ∫.Inverses ∫inv

  inv : Inverses f g
  inv = record  { invl = ap ∫Hom.fst ∫inv.invl ; invr = ap ∫Hom.fst ∫inv.invr }
  
  inv' : Inverses[ inv ] f' g'
  inv' = record { invl' = ap ∫Hom.snd ∫inv.invl ; invr' = ap ∫Hom.snd ∫inv.invr }

∫Inverses-iso {f = f} {g} {f'} {g'} = unc , iso DInverses rinv linv where
  unc : _ → _
  unc (_ , inv') = ∫Inverses inv'

  rinv : is-right-inverse DInverses unc
  rinv _ = refl

  linv : is-left-inverse DInverses unc
  linv _ = Σ-path refl (Inverses[]-are-prop _ _ _ _ _)

Dis-invertible
  : ∀ {x y x' y'} {∫f : ∫.Hom (x , x') (y , y')}
  → ∫.is-invertible ∫f
  → Σ (is-invertible (∫f .∫Hom.fst)) λ f-inv
    → is-invertible[ f-inv ] (∫f .∫Hom.snd)
Dis-invertible {∫f = ∫hom f f'} ∫f-inv = f-inv , f'-inv where
  module ∫f-inv = ∫.is-invertible ∫f-inv

  f-inv : is-invertible f
  f-inv = record 
    { inv = ∫f-inv.inv .∫Hom.fst ; inverses = DInverses ∫f-inv.inverses .fst }
  
  f'-inv : is-invertible[ f-inv ] f'
  f'-inv = record 
    { inv' = ∫f-inv.inv .∫Hom.snd ; inverses' = DInverses ∫f-inv.inverses .snd }

∫is-invertible-iso {f = f} {f'} = unc , iso Dis-invertible rinv linv where
  unc : _ → _
  unc (_ , f'-inv) = ∫is-invertible f'-inv

  rinv : is-right-inverse Dis-invertible unc
  rinv _ = refl

  linv : is-left-inverse Dis-invertible unc
  linv _ = Σ-path refl (is-invertible[]-is-prop _ _ _ _)

D≅
  : ∀ {x y} {x' : Ob[ x ]} {y' : Ob[ y ]}
  → (x , x') ∫.≅ (y , y')
  → Σ (x ≅ y) λ x≅y → x' ≅[ x≅y ] y'
D≅ {x} {y} {x'} {y'} ∫x≅∫y = x≅y , x'≅y' where
  module ∫x≅∫y = ∫._≅_ ∫x≅∫y

  x≅y : x ≅ y
  x≅y .to = ∫x≅∫y.to .∫Hom.fst
  x≅y .from = ∫x≅∫y.from .∫Hom.fst
  x≅y .inverses = DInverses ∫x≅∫y.inverses .fst

  x'≅y' : x' ≅[ x≅y ] y'
  x'≅y' .to' = ∫x≅∫y.to .∫Hom.snd
  x'≅y' .from' = ∫x≅∫y.from .∫Hom.snd
  x'≅y' .inverses' = DInverses ∫x≅∫y.inverses .snd

∫≅-iso {x} {y} {x'} {y'} = unc , iso D≅ rinv linv where
  unc : _ → _
  unc (_ , x'≅y') = ∫≅ x'≅y'

  rinv : is-right-inverse D≅ unc
  rinv _ = refl

  linv : is-left-inverse D≅ unc
  linv (x≅y , x'≅y') = Σ-path refl (≅[]-path (ap to' (transport-refl x'≅y')))
```
</details>