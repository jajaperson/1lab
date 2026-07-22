<!--
```agda
open import 1Lab.Equiv
open import 1Lab.Type.Sigma

open import Cat.Functor.Equivalence
open import Cat.Functor.Naturality.Reflection
open import Cat.Functor.Naturality
open import Cat.Displayed.Functor
open import Cat.Instances.Product
open import Cat.Displayed.Functor.Total
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

open Displayed-functor
open is-precat-iso
```
-->

```agda
module Cat.Displayed.Instances.TotalProduct where
```

# Total product displayed categories {defines=total-product-category}

If $\cE\to \cB$ and $q :\cD \to \cC$ are displayed categories, then we
can define their **total product** $\cE \times^{TD} \cD\ \liesover \cB
\times^c \cC$, which is again a displayed category. Just as the ordinary
[[product category]] comes equipped with functors `Fst`{.Agda} and
`Snd`{.Agda} satisfying a universal property analogous to categorical
[[product diagrams]], the total product comes equipped with displayed
functors `Fstᵀᴰ`{.Agda} and `Sndᵀᴰ`{.Agda} satisfying a universal
property analogous to, you guessed it, [[total product diagrams]].

<!--
```agda
private
  variable
    o ℓ o' ℓ' o'' ℓ'' : Level
    A B C D : Precategory o ℓ
    ℰ ℱ 𝒢 ℋ : Displayed A o ℓ
```
-->

```agda
_×ᵀᴰ_ : Displayed A o ℓ → Displayed B o' ℓ' → Displayed (A ×ᶜ B) (o ⊔ o') (ℓ ⊔ ℓ')
ℰ ×ᵀᴰ ℱ = prodcat' module ×ᵀᴰ where
```

<!--
```agda
  module ℰ = Displayed ℰ
  module ℱ = Displayed ℱ
```
-->

```agda
  prodcat' : Displayed _ _ _
  prodcat' .Displayed.Ob[_] (p₁ , p₂) = ℰ.Ob[ p₁ ] × ℱ.Ob[ p₂ ]
  prodcat' .Displayed.Hom[_] (f₁ , f₂) (c₁ , c₂) (d₁ , d₂) =
    ℰ.Hom[ f₁ ] c₁ d₁ × ℱ.Hom[ f₂ ] c₂ d₂
  prodcat' .Displayed.id' = (ℰ.id' , ℱ.id')
  prodcat' .Displayed.Hom[_]-set _ _ _ = hlevel 2
  prodcat' .Displayed._∘'_ (f₁ , f₂) (g₁ , g₂) =
    ℰ._∘'_ f₁ g₁ , ℱ._∘'_ f₂ g₂
  prodcat' .Displayed.idr' (f₁ , f₂) = ℰ.idr' f₁ ,ₚ ℱ.idr' f₂
  prodcat' .Displayed.idl' (f₁ , f₂) = ℰ.idl' f₁ ,ₚ ℱ.idl' f₂
  prodcat' .Displayed.assoc' (f₁ , f₂) (g₁ , g₂) (h₁ , h₂) =
    ℰ.assoc' f₁ g₁ h₁ ,ₚ ℱ.assoc' f₂ g₂ h₂
  prodcat' .Displayed.hom[_] p f = ℰ.hom[ ap fst p ] (f .fst) ,  ℱ.hom[ ap snd p ] (f .snd)
  prodcat' .Displayed.coh[_] p f = ℰ.coh[ ap fst p ] (f .fst) ,ₚ ℱ.coh[ ap snd p ] (f .snd)
```

<!--
```agda
{-# DISPLAY ×ᵀᴰ.prodcat' a b = a ×ᵀᴰ b #-}
infixr 20 _×ᵀᴰ_
```
-->

```agda
Fstᵀᴰ : Displayed-functor Fst (ℰ ×ᵀᴰ ℱ) ℰ
Fstᵀᴰ .F₀' = fst
Fstᵀᴰ .F₁' = fst
Fstᵀᴰ .F-id' = refl
Fstᵀᴰ .F-∘' = refl

Sndᵀᴰ : Displayed-functor Snd (ℰ ×ᵀᴰ ℱ) ℱ
Sndᵀᴰ .F₀' = snd
Sndᵀᴰ .F₁' = snd
Sndᵀᴰ .F-id' = refl
Sndᵀᴰ .F-∘' = refl
```

We proceed analogously to as in [[product categories]].

```
DisCat⟨_,_⟩
  : ∀ {F G} → Displayed-functor F ℰ ℱ → Displayed-functor G ℰ 𝒢
  → Displayed-functor Cat⟨ F , G ⟩ ℰ (ℱ ×ᵀᴰ 𝒢)
DisCat⟨ F' , G' ⟩ = f' module DisCat⟨,⟩ where
  f' : Displayed-functor _ _ _
  f' .F₀' = ⟨ F' .F₀' , G' .F₀' ⟩
  f' .F₁' = ⟨ F' .F₁' , G' .F₁' ⟩
  f' .F-id' = F' .F-id' ,ₚ G' .F-id'
  f' .F-∘' = F' .F-∘' ,ₚ G' .F-∘'

Swapᵀᴰ : Displayed-functor Swap (ℰ ×ᵀᴰ ℱ) (ℱ ×ᵀᴰ ℰ)
Swapᵀᴰ = DisCat⟨ Sndᵀᴰ , Fstᵀᴰ ⟩

_F×ᵀᴰ_
  : ∀ {F G} → Displayed-functor F ℰ 𝒢 → Displayed-functor G ℱ ℋ
  → Displayed-functor (F F× G)  (ℰ ×ᵀᴰ ℱ) (𝒢 ×ᵀᴰ ℋ)
F' F×ᵀᴰ G' = f' module F×ᵀᴰ where
  f' : Displayed-functor _ _ _
  f' .F₀' = ×-map (F' .F₀') (G' .F₀')
  f' .F₁' = ×-map (F' .F₁') (G' .F₁')
  f' .F-id' = F' .F-id' ,ₚ G' .F-id'
  f' .F-∘' = F' .F-∘' ,ₚ G' .F-∘'
```

<!--
```agda
{-# DISPLAY DisCat⟨,⟩.f' F' G' = DisCat⟨ F' , G' ⟩ #-}
{-# DISPLAY F×ᵀᴰ.f' F' G' = F' F×ᵀᴰ G' #-}
```
-->

## Total products and total categories

The [[total category]] of $\cE \times^{TD} \cF$ is [[precategory
isomorphism|isomorphic]] to the ordinary [[product category]] $\int \cE \times^c \int
\cF$.

```agda
module _ {ℰ : Displayed A o ℓ} {ℱ : Displayed B o' ℓ'} where
  ∫×ᵀᴰ→ : Functor (∫ (ℰ ×ᵀᴰ ℱ)) (∫ ℰ ×ᶜ ∫ ℱ)
  ∫×ᵀᴰ→ = Cat⟨ ∫ᶠ Fstᵀᴰ , ∫ᶠ Sndᵀᴰ ⟩

  ∫×ᵀᴰ-precat-iso : is-precat-iso ∫×ᵀᴰ→
  ∫×ᵀᴰ-precat-iso .has-is-ff = is-iso→is-equiv $ iso (λ _ → _) (λ _ → refl) (λ _ → refl)
  ∫×ᵀᴰ-precat-iso .has-is-iso = is-iso→is-equiv $ iso (λ _ → _) (λ _ → refl) (λ _ → refl)

  ∫×ᵀᴰ-is-equiv : is-equivalence ∫×ᵀᴰ→
  ∫×ᵀᴰ-is-equiv = is-precat-iso→is-equivalence ∫×ᵀᴰ-precat-iso

  ∫×ᵀᴰ← : Functor (∫ ℰ ×ᶜ ∫ ℱ) (∫ (ℰ ×ᵀᴰ ℱ))
  ∫×ᵀᴰ← = is-equivalence.F⁻¹ ∫×ᵀᴰ-is-equiv
```

Recall that taking total categories gives lets us view the notion of a
displayed category $\cE \liesover \cA$ as equivalent to a functor $\pi :
\int \cE \to \cA$. Under this equivalence, total products become
`product functors`{.Agda ident="_×F_"}.

```agda
  πᶠ≅πᶠ×πᶠ : πᶠ (ℰ ×ᵀᴰ ℱ) ≅ⁿ ((πᶠ ℰ F× πᶠ ℱ) F∘ ∫×ᵀᴰ→)
  πᶠ≅πᶠ×πᶠ = trivial-isoⁿ!
```
