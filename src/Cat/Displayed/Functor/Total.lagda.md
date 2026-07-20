<!--
```agda
open import Cat.Functor.Naturality.Reflection
open import Cat.Displayed.Instances.Functor
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
  ∫ᶠ .F-id = ∫Hom-path ℱ _ (F' .F-id')
  ∫ᶠ .F-∘ (∫hom f f') (∫hom g g') = ∫Hom-path ℱ _ (F' .F-∘')
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
```
-->

```agda
  ∫ᶠId'≅Id : ∫ᶠ (Id' {ℰ = ℰ}) ≅ⁿ Id
  ∫ᶠId'≅Id = trivial-isoⁿ!
```

Similarly, the total of the composite of two displayed functors is the
composite of the total functors.

<!--
```agda
module _
  {oa ℓa ob ℓb oc ℓc oe ℓe of ℓf og ℓg}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb} {C : Precategory oc ℓc}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf} {𝒢 : Displayed C og ℓg}
  {F : Functor B C} {G : Functor A B}
  {F' : Displayed-functor F ℱ 𝒢} {G' : Displayed-functor G ℰ ℱ}
  where
```
-->

```agda
  ∫ᶠ∘ : ∫ᶠ (F' F∘' G') ≅ⁿ ∫ᶠ F' F∘ ∫ᶠ G'
  ∫ᶠ∘ = trivial-isoⁿ!
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
  ∫ⁿ = record where
    η (x , x') = ∫hom _ (η' x')
    is-natural (x , x') (y , y') (∫hom f f') = ∫Hom-path ℱ _ (is-natural' x' y' f')
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

The total natural transformation of the displayed identity natural
transformation is, of course, the identity natural transformation of
the total functor.

<!--
```agda
module _
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B} {F' : Displayed-functor F ℰ ℱ}
  where
```
-->

```agda
  ∫ⁿidnt'≡idnt : Path (∫ᶠ F' => ∫ᶠ F') (∫ⁿ idnt') idnt
  ∫ⁿidnt'≡idnt = trivial!
```

Similarly, the total of the composite of two natural transformations is
the composite of the total natural transformations.

<!--
```agda
module _
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B} {F' : Displayed-functor F ℰ ℱ}
  {G : Functor A B} {G' : Displayed-functor G ℰ ℱ}
  {H : Functor A B} {H' : Displayed-functor H ℰ ℱ}
  where
```
-->

```agda
  ∫ⁿ∘
    : ∀ {β α} (β' : G' =[ β ]=> H') (α' : F' =[ α ]=> G')
    → ∫ⁿ (β' ∘nt' α') ≡ ∫ⁿ β' ∘nt ∫ⁿ α'
  ∫ⁿ∘ β' α' = trivial!
```

## Functoriality

<!--
```agda
module _
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  where
```
-->

We can combine the operations of taking total functors and total
natural transformations into a _functor_ from the [[total category]] of
the [[displayed functor category]] $[\cE , \cF]$ to the ordinary
[[functor category]] $[\int \cE , \int \cF]$.

```agda
  ∫ᶠⁿ : Functor (∫ DisCat[ ℰ , ℱ ]) Cat[ ∫ ℰ , ∫ ℱ ]
  ∫ᶠⁿ .F₀ (_ , F') = ∫ᶠ F'
  ∫ᶠⁿ .F₁ (∫hom _ α') = ∫ⁿ α'
  ∫ᶠⁿ .F-id = ∫ⁿidnt'≡idnt
  ∫ᶠⁿ .F-∘ (∫hom _ β') (∫hom _ α') = ∫ⁿ∘ β' α'
```
