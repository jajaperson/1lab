<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Displayed.Functor
open import Cat.Displayed.Total
open import Cat.Functor.Compose
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Prelude

open Displayed-functor
open Functor
```
-->

```agda
module Cat.Displayed.Functor.Total where
```

# Total functor {defines="total-functor"}

Given [[displayed categories]] $\cE \liesover \cA$ and $\cF \liesover
\cB$, and a [[displayed functor]] $F' : \cE \to \cF$ over $F : \cA \to
\cB$, we can recover an ordinary [[functor]] $\int F : \int \cE \to \int
\cF$ between [[total categories]].

<!--
```agda
module _
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B} (F' : Displayed-functor F ℰ ℱ)
  where
```
-->

```agda
  ∫ᶠ : Functor (∫ ℰ) (∫ ℱ)
  ∫ᶠ .F₀ (x , x') = ₀ F x , ₀' F' x'
  ∫ᶠ .F₁ (∫hom f f') = ∫hom _ (₁' F' f')
  ∫ᶠ .F-id = ∫Hom-path ℱ _ $ F' .F-id'
  ∫ᶠ .F-∘ (∫hom f f') (∫hom g g') = ∫Hom-path ℱ _ $ F' .F-∘'
```

The total functor respects the projection `πᶠ`{.Agda} to the base
category so that

~~~{.quiver .attach-around}
\begin{tikzcd}
	{\int \cE} && {\int \cF} \\
	\\
	\cA && \cB
	\arrow["{\int F'}", from=1-1, to=1-3]
	\arrow["{\pi_{\cE}}"', from=1-1, to=3-1]
	\arrow["{\pi_\cF}", from=1-3, to=3-3]
	\arrow["F"', from=3-1, to=3-3]
\end{tikzcd}
~~~

commutes.

```agda
  ∫ᶠ-preserves-base : F F∘ (πᶠ ℰ) ≡ (πᶠ ℱ) F∘ ∫ᶠ
  ∫ᶠ-preserves-base = Functor-path (λ x → refl) (λ f → refl)
```

Indeed, a displayed functor $F'$ over $F$ can be thought of as a
repackaging of the data of a functor $\int F'$ for which this diagram
commutes.

The total functor of the displayed identity functor `Id'`{.Agda} is of
course the ordinary identity functor `Id`{.Agda}.

<!--
```agda
module _
  {oa ℓa oe ℓe}
  {A : Precategory oa ℓa} {ℰ : Displayed A oe ℓe}
  where
  private
    module A = Precategory A
    module ℰ = Displayed ℰ
    module ∫ℰ = Precategory (∫ ℰ)
```
-->

```agda
  ∫ᶠId'≅Id : ∫ᶠ (Id' {ℰ = ℰ}) ≅ⁿ Id
  ∫ᶠId'≅Id = to-natural-iso record where
    eta x = ∫ℰ.id
    inv x = ∫ℰ.id
    eta∘inv x = ∫ℰ.idl ∫ℰ.id
    inv∘eta x = ∫ℰ.idl ∫ℰ.id
    natural x y f =
      f ∫ℰ.∘ ∫ℰ.id  ≡⟨ ∫ℰ.idr f ⟩
      f             ≡˘⟨ ∫ℰ.idl f ⟩
      ∫ℰ.id ∫ℰ.∘ f  ∎
```

Similarly, the composite of two total functors is the total of the
composite.

<!--
```agda
module _
  {oa ℓa ob ℓb oc ℓc oe ℓe of ℓf og ℓg}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb} {C : Precategory oc ℓc}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf} {𝒢 : Displayed C og ℓg}
  {F : Functor B C} {G : Functor A B}
  {F' : Displayed-functor F ℱ 𝒢} {G' : Displayed-functor G ℰ ℱ}
  where
  private
    module A = Precategory A
    module ℰ = Displayed ℰ
    module ∫ℰ = Precategory (∫ ℰ)
    module B = Precategory B
    module ℱ = Displayed ℱ
    module ∫ℱ = Precategory (∫ ℱ)
    module C = Precategory A
    module 𝒢 = Displayed 𝒢
    module ∫𝒢 = Precategory (∫ 𝒢)
```
-->

```agda
  ∫ᶠ∘ : ∫ᶠ (F' F∘' G') ≅ⁿ ∫ᶠ F' F∘ ∫ᶠ G'
  ∫ᶠ∘ = to-natural-iso record where
    eta x = ∫𝒢.id
    inv x = ∫𝒢.id
    eta∘inv x = ∫𝒢.idl ∫𝒢.id
    inv∘eta x = ∫𝒢.idl ∫𝒢.id
    natural x y f =
      ₁ (∫ᶠ F' F∘ ∫ᶠ G') f ∫𝒢.∘ ∫𝒢.id ≡⟨ ∫𝒢.idr (₁ (∫ᶠ F' F∘ ∫ᶠ G') f) ⟩
      ₁ (∫ᶠ (F' F∘' G')) f            ≡˘⟨ ∫𝒢.idl (₁ (∫ᶠ F' F∘ ∫ᶠ G') f) ⟩
      ∫𝒢.id ∫𝒢.∘ ₁ (∫ᶠ (F' F∘' G')) f ∎
```

## Total natural transformations {defines="total-natural-transformation"}

Suppose we have an additional [[displayed functor]] $G' : \cE \to \cF$
over $G : \cA \to \cB$, and a [[displayed natural transformation]]
$\eta' : F' \To G'$ over $\eta : F \To G$. We can then similarly recover
an ordinary [[natural transformation]] $\int \eta : \int F \To \int G$
between [[total functors]]:

<!--
```agda
module _
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F G : Functor A B} {ηⁿ : F => G}
  {F' : Displayed-functor F ℰ ℱ}
  {G' : Displayed-functor G ℰ ℱ}
  (η'ⁿ : F' =[ ηⁿ ]=> G')
  where

  open _=>_ ηⁿ
  open _=[_]=>_ η'ⁿ
```
-->

```agda
  ∫ⁿ : ∫ᶠ F' => ∫ᶠ G'
  ∫ⁿ = NT
    (λ (x , x') → ∫hom _ (η' x'))
    λ (x , x') (y , y') (∫hom f f') → ∫Hom-path ℱ _ $ is-natural' x' y' f'
```

Applying the projection `πᶠ`{.Agda} to the total natural transformation
$\int\eta'$ gives back $\eta$ in the following sense:

```agda
  ∫ⁿ-preserves-base : PathP
    (λ i → ∫ᶠ-preserves-base F' i => ∫ᶠ-preserves-base G' i)
    (ηⁿ ◂ πᶠ ℰ) (πᶠ ℱ ▸ ∫ⁿ)
  ∫ⁿ-preserves-base = Nat-pathp
    (∫ᶠ-preserves-base F') (∫ᶠ-preserves-base G') λ x → refl
```

# Total functor of a vertical functor

<!--
```agda
module _ 
  {oa ℓa oe ℓe of ℓf}
  {A : Precategory oa ℓa} {ℰ : Displayed A oe ℓe} {ℱ : Displayed A of ℓf}
  (F' : Vertical-functor ℰ ℱ)
  where
```
-->

The same constructions work mutatis mutandis for [[vertical functors]]
and [[vertical natural transformations]].

```agda
  ∫ᶠ↓ : Functor (∫ ℰ) (∫ ℱ)
  ∫ᶠ↓ = ∫ᶠ F'
```

<!--
```agda
module _
  {oa ℓa oe ℓe of ℓf}
  {A : Precategory oa ℓa} {ℰ : Displayed A oe ℓe} {ℱ : Displayed A of ℓf}
  {F' : Vertical-functor ℰ ℱ}
  {G' : Vertical-functor ℰ ℱ}
  (η'ⁿ : F' =>↓ G')
  where

  open _=>↓_ η'ⁿ
```
-->

```agda
  ∫ⁿ↓ : ∫ᶠ↓ F' => ∫ᶠ↓ G'
  ∫ⁿ↓ = NT
    (λ (x , x') → ∫hom _ (η' x'))
    λ (x , x') (y , y') (∫hom f f') → ∫Hom-path ℱ _ $ is-natural' x' y' f'
```
