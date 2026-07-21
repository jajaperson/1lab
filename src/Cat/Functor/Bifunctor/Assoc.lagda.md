<!--
```agda
open import Cat.Functor.Bifunctor
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Functor.Compose
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Morphism as Cm

open Functor
```
-->

```agda
module Cat.Functor.Bifunctor.Assoc
  {o ℓ ℓ'}
  {O : Type o}
  (H : O → O → Precategory ℓ ℓ')
  (F : ∀ {A B C} → Bifunctor (H B C) (H A B) (H A C))
  where
```

# Associations of nested bifunctors

Given a [[bifunctor]] $F : \cC \times \cC \to \cC$, we can consider left
and right associations forming _trifunctors_ $F(F(-, -), -)$ and $F(-,
F(-, -))$. We can generalise this situation slightly, to a family
`F`{.Agda} of bifunctors defined on a family `H`{.Agda} of categories.

<!--
```agda
private module F {A B C} where
  open Bifunctor (F {A} {B} {C}) public
  open Fr (F {A} {B} {C}) public
```
-->

```agda
module _ {A B C D} where

  assocˡ : Functor (H C D ×ᶜ H B C ×ᶜ H A B) (H A D)
  assocˡ .F₀ (x , y , z) = F · (F · x · y) · z
  assocˡ .F₁ (f , g , h) = (f F.◆ g) F.◆ h
  assocˡ .F-id = ap₂ F._◆_ F.◆-id refl ∙ F.◆-id
  assocˡ .F-∘ f g = ap₂ F._◆_ F.◆-∘ refl ∙ F.◆-∘

  assocʳ : Functor (H C D ×ᶜ H B C ×ᶜ H A B) (H A D)
  assocʳ .F₀ (x , y , z) = F · x · (F · y · z)
  assocʳ .F₁ (f , g , h) = f F.◆ (g F.◆ h)
  assocʳ .F-id = ap₂ F._◆_ refl F.◆-id ∙ F.◆-id
  assocʳ .F-∘ f g = ap₂ F._◆_ refl F.◆-∘ ∙ F.◆-∘
```

A witness of the associativity of such a bifunctor is a natural
isomorphism between these two associations.

```agda
Associator-for : Type _
Associator-for = ∀ {A B C D} →
  let open Cm Cat[ H C D ×ᶜ H B C ×ᶜ H A B , H A D ]
  in assocˡ ≅ assocʳ
```
