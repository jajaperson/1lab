<!--
```agda
open import Cat.Displayed.Functor.Bifunctor
open import Cat.Displayed.Functor
open import Cat.Functor.Bifunctor
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.Functor.Bifunctor.Total where
```

# Total bifunctor

<!--
```agda
module _
  {oa ℓa ob ℓb oc ℓc oe ℓe of ℓf og ℓg}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb} {C : Precategory oc ℓc}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf} {𝒢 : Displayed C og ℓg}
  {F : Bifunctor A B C} (F' : Displayed-bifunctor F ℰ ℱ 𝒢)
  where

  private
    module F = Bifunctor F
    module F' = Displayed-bifunctor F'
```
-->

```agda
  ∫ᵇᶠ : Bifunctor (∫ ℰ) (∫ ℱ) (∫ 𝒢)
  ∫ᵇᶠ = make-bifunctor record where
    F₀ (a , a') (b , b') = F · a · b , F' · a' · b'
    lmap (∫hom f f') = ∫hom (F.lmap f) (F'.lmap' f')
    rmap (∫hom f f') = ∫hom (F.rmap f) (F'.rmap' f')
    lmap-id = ∫Hom-path 𝒢 F.lmap-id F'.lmap-id'
    rmap-id = ∫Hom-path 𝒢 F.rmap-id F'.rmap-id'
    lmap-∘ (∫hom f f') (∫hom g g') = ∫Hom-path 𝒢 (F.lmap-∘ f g) F'.lmap-∘'
    rmap-∘ (∫hom f f') (∫hom g g') = ∫Hom-path 𝒢 (F.rmap-∘ f g) F'.rmap-∘'
    lrmap (∫hom f f') (∫hom g g') = ∫Hom-path 𝒢 (F.lrmap f g) (F'.lrmap' f' g')
```
