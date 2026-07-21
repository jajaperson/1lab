<!--
```agda
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Equivalence
open import Cat.Instances.Product
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.Instances.TotalProduct {o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ o₄ ℓ₄}
  {C : Precategory o₁ ℓ₁} {D : Precategory o₂ ℓ₂}
  (ℰ : Displayed C o₃ ℓ₃) (ℱ : Displayed D o₄ ℓ₄)
  where
```

<!--
```agda
private module ℰ = Displayed ℰ
private module ℱ = Displayed ℱ

open Functor
open is-precat-iso
```
-->

# The total product of displayed categories

If $\cE\to \cB$ and $q :\cD \to \cC$ are
displayed categories, then we can define their **total product**
$\cE\times \cD\to \cB\times \cC$,
which is again a displayed category.

```agda
_×ᵀᴰ_ : Displayed (C ×ᶜ D) (o₃ ⊔ o₄) (ℓ₃ ⊔ ℓ₄)
```

If displayed categories are regarded as functors, then the product of
displayed categories can be regarded as the usual product of functors.

```agda
_×ᵀᴰ_ .Displayed.Ob[_] (p₁ , p₂) =
  ℰ.Ob[ p₁ ]  × ℱ.Ob[ p₂ ]
_×ᵀᴰ_ .Displayed.Hom[_] (f₁ , f₂) (c₁ , c₂) (d₁ , d₂) =
  ℰ.Hom[ f₁ ] c₁ d₁ ×
  ℱ.Hom[ f₂ ] c₂ d₂
_×ᵀᴰ_ .Displayed.id' = (ℰ.id' , ℱ.id')
```

We establish that the hom sets of the product fibration are actually
sets.

If $x, y : \operatorname{Ob}[C \times D]$ (so $x = (x_C, x_D), y = (y_C,
y_D)$) and $f : x \to y$ (so $f$ is $(f_C, f_D)$) then for any two
morphisms $f_1,f_2$ lying over $f$, and any $p, q : f_1 = f_2$, $p=q$.

```agda
_×ᵀᴰ_ .Displayed.Hom[_]-set _ _ _ = hlevel 2
```

Composition is pairwise.

```agda
_×ᵀᴰ_ .Displayed._∘'_ (f₁ , f₂) (g₁ , g₂) =
  ℰ._∘'_ f₁ g₁ , ℱ._∘'_ f₂ g₂
```

Associativity and left/right identity laws hold because
they hold for the components of the ordered pairs.

```agda
_×ᵀᴰ_ .Displayed.idr' (f₁ , f₂) = ℰ.idr' f₁ ,ₚ ℱ.idr' f₂
_×ᵀᴰ_ .Displayed.idl' (f₁ , f₂) = ℰ.idl' f₁ ,ₚ ℱ.idl' f₂
_×ᵀᴰ_ .Displayed.assoc' (f₁ , f₂) (g₁ , g₂) (h₁ , h₂) =
  ℰ.assoc' f₁ g₁ h₁ ,ₚ ℱ.assoc' f₂ g₂ h₂
```

```agda
_×ᵀᴰ_ .Displayed.hom[_] p f = ℰ.hom[ ap fst p ] (f .fst) ,  ℱ.hom[ ap snd p ] (f .snd)
_×ᵀᴰ_ .Displayed.coh[_] p f = ℰ.coh[ ap fst p ] (f .fst) ,ₚ ℱ.coh[ ap snd p ] (f .snd)
```

<!--
```agda
infixr 20 _×ᵀᴰ_
```
-->

## Total products and total categories

The reason we refer to this construction as the total product is that
its [[total category]] is [[isomorphic|isomorphism of precategories]] to
the ordinary [[product|product category]] of total categories.

```agda
∫×ᵀᴰ→∫×ᶜ∫ : Functor (∫ _×ᵀᴰ_) (∫ ℰ ×ᶜ ∫ ℱ)
∫×ᵀᴰ→∫×ᶜ∫ .F₀ ((x , y) , x' , y') = (x , x') , y , y'
∫×ᵀᴰ→∫×ᶜ∫ .F₁ (∫hom (f , g) (f' , g')) = ∫hom f f' , ∫hom g g'
∫×ᵀᴰ→∫×ᶜ∫ .F-id = refl
∫×ᵀᴰ→∫×ᶜ∫ .F-∘ _ _ = refl

∫×ᵀᴰ→∫×ᶜ∫-is-iso : is-precat-iso ∫×ᵀᴰ→∫×ᶜ∫
∫×ᵀᴰ→∫×ᶜ∫-is-iso .has-is-ff = is-iso→is-equiv $ iso
  (λ (∫hom f f' , ∫hom g g') → ∫hom (f , g) (f' , g'))
  (λ _ → refl) λ _ → refl
∫×ᵀᴰ→∫×ᶜ∫-is-iso .has-is-iso = is-iso→is-equiv $ iso
  (λ ((x , x') , y , y') → (x , y) , x' , y')
  (λ _ → refl) λ _ → refl
```

This induces a [[path between precategories]]

```agda
∫×ᵀᴰ≡∫×ᶜ∫ : ∫ _×ᵀᴰ_ ≡ ∫ ℰ ×ᶜ ∫ ℱ
∫×ᵀᴰ≡∫×ᶜ∫ = Precategory-path ∫×ᵀᴰ→∫×ᶜ∫ ∫×ᵀᴰ→∫×ᶜ∫-is-iso
```

and [[adjoint equivalence]]

```agda
∫×ᵀᴰ→∫×ᶜ∫-is-equiv : is-equivalence ∫×ᵀᴰ→∫×ᶜ∫
∫×ᵀᴰ→∫×ᶜ∫-is-equiv = is-precat-iso→is-equivalence ∫×ᵀᴰ→∫×ᶜ∫-is-iso

∫×ᶜ∫→∫×ᵀᴰ : Functor (∫ ℰ ×ᶜ ∫ ℱ) (∫ _×ᵀᴰ_)
∫×ᶜ∫→∫×ᵀᴰ = is-equivalence.F⁻¹ ∫×ᵀᴰ→∫×ᶜ∫-is-equiv
```
