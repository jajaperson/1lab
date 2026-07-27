<!--
```agda
open import Cat.Displayed.Functor
open import Cat.Functor.Naturality.Reflection
open import Cat.Functor.Equivalence
open import Cat.Functor.Naturality
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Univalent
open import Cat.Prelude

import Cat.Reasoning as Cr
import Cat.Displayed.Reasoning as Dr
```
-->

```agda
module Cat.Displayed.Instances.Antitotal {o ℓ} (B : Precategory o ℓ) where
```

<!--
```agda
private
  variable o' ℓ' : Level
  module B = Cr B
```
-->

# Displayed categories from a functor

Fixing a base category $\cB$, a [[displayed category]] $\cE$ over $\cB$
is often introduced as a type-theoretic repackaging of a [[functor]]
$\pi : \int \cE \to \cF$ for some ordinary category $\int \cE$. To
recover $\int \cE$ and $\pi$ from a displayed category $\cB$, we take
the [[total category]] with its projection, but what about going the
other direction?

Suppose $\cE^T$ it a category and $F : \cE^T \to B$ a functor.

```agda
module _ {ℰᵀ : Precategory o' ℓ'} (F : Functor ℰᵀ B) where
```

<!--
```agda
  open Displayed

  private
    module ℰᵀ = Precategory ℰᵀ
    module F = Functor F
```
-->

We construct a displayed category $\cE$ where the type of objects
$\cE_x$ over $x$ is the [[fibre]] of $F_0$ over $x$, that is the type of
objects $x' : \cE^T$ equipped with a path $F_0 x = x'$.

```agda
  Antitotal : Displayed B (o ⊔ o') (ℓ ⊔ ℓ')
  Antitotal .Ob[_] = fibre F.₀
```

The morphisms $\cE_f((x', p), (y', q))$ are defined similarly, as the
type of morphisms $f' : \cE^T$ equipped with a path from $F_1 f'$ to $f$
_over_ the paths $p$ and $q$.

```agda
  Antitotal .Hom[_] f (x' , Fx'=x) (y' , Fy'=y) =
      Σ (ℰᵀ.Hom x' y') λ f' → PathP (λ i → B.Hom (Fx'=x i) (Fy'=y i)) (F.₁ f') f
  Antitotal .Hom[_]-set _ _ _ = hlevel 2
```

Identity and composition are simply those of $\cE^T$, where we construct
the required paths using [[path induction]].

```agda
  Antitotal .id' {x} {x' , Fx'=x} = ℰᵀ.id , J
    (λ x Fx'=x → PathP (λ i → B.Hom (Fx'=x i) (Fx'=x i)) (F.₁ ℰᵀ.id) B.id)
    F.F-id Fx'=x

  Antitotal ._∘'_ {x = _ , Fx'=x} {_ , Fy'=y} {_ , Fz'=z} {f} {g} (f' , Ff'=f) (g' , Fg'=g) =
    f' ℰᵀ.∘ g' , J₃
      (λ x y z Fx'=x Fy'=y Fz'=z →
        ∀ f g
          → PathP (λ i → B.Hom (Fy'=y i) (Fz'=z i)) (F.₁ f') f
          → PathP (λ i → B.Hom (Fx'=x i) (Fy'=y i)) (F.₁ g') g
          → PathP (λ i → B.Hom (Fx'=x i) (Fz'=z i)) (F.₁ (f' ℰᵀ.∘ g')) (f B.∘ g))
      (λ f g Ff'=f Fg'=g → J₂
        (λ f g Ff'=f Fg'=g → F.₁ (f' ℰᵀ.∘ g') ≡ f B.∘ g)
        (F.F-∘ f' g') Ff'=f Fg'=g)
      Fx'=x Fy'=y Fz'=z f g Ff'=f Fg'=g
```

The identity and associativity laws follow from those of $\cE^T$ and
`ℰᵀ.Hom-set`{.Agda}.

```agda
  Antitotal .idr' (f' , _) = Σ-prop-pathp! (ℰᵀ.idr f')
  Antitotal .idl' (f' , _) = Σ-prop-pathp! (ℰᵀ.idl f')
  Antitotal .assoc' (f' , _) (g' , _) (h' , _) = Σ-prop-pathp! (ℰᵀ.assoc f' g' h')
```

We define homwise transport so that only the path data are affected.

```agda
  Antitotal .hom[_] p (f' , Ff'=f) = f' , Ff'=f ▷ p
  Antitotal .coh[_] p (f' , Ff'=f) = Σ-prop-pathp! refl
```

<!--
```agda
  _ = ℰᵀ.Hom-set
```
-->

## Total of the antitotal

Taking the [[total category]] $\int \cE$ of $\cE$ gets us a precategory
which is [[isomorphic|isomorphism of precategories]] and [[hence
identical|path between precategories]] to our orginal category $\cE^T$.

<!--
```agda
  open Functor
  open is-precat-iso
```
-->

```agda
  ∫Antitotal→ : Functor (∫ Antitotal) ℰᵀ
  ∫Antitotal→ .F₀ (_ , x' , _) = x'
  ∫Antitotal→ .F₁ (∫hom _ (f' , _)) = f'
  ∫Antitotal→ .F-id = refl
  ∫Antitotal→ .F-∘ _ _ = refl

  ∫Antitotal-is-iso : is-precat-iso ∫Antitotal→
  ∫Antitotal-is-iso .has-is-ff {x , x' , Fx'=x} {y , y' , Fy'=y} = J₂
    (λ x y Fx'=x Fy'=y → is-equiv (∫Antitotal→ .F₁ {x , x' , Fx'=x} {y , y' , Fy'=y}))
    (is-iso→is-equiv $ iso
      (λ f' → ∫hom (F.F₁ f') (f' , refl))
      (λ _ → refl)
      λ (∫hom _ (_ , Ff'=f)) → ∫Hom-path Antitotal Ff'=f (Σ-prop-pathp! refl))
    Fx'=x Fy'=y
  ∫Antitotal-is-iso .has-is-iso = is-iso→is-equiv $ iso
    (λ x' → (F.₀ x') , x' , refl)
    (λ _ → refl) λ (x , x' , Fx'=x) → J
      (λ x Fx'=x → (F.₀ x' , x' , refl) ≡ (x , x' , Fx'=x))
      refl Fx'=x

  ∫Antitotal-is-equiv : is-equivalence ∫Antitotal→
  ∫Antitotal-is-equiv = is-precat-iso→is-equivalence ∫Antitotal-is-iso

  ∫Antitotal← : Functor ℰᵀ (∫ Antitotal)
  ∫Antitotal← = ∫Antitotal-is-equiv .is-equivalence.F⁻¹
```

Furthermore, “over” this identification $\int \cE \cong \cE^T$, we have
an equivalence of the projection $\pi : \int \cE \to \cB$ with the
functor $F : \cE^T \to \cB$, giving a natural isomorphism as depicted
below.

~~~{.quiver}
\[\begin{tikzcd}
	{\int \cE} && {\cE^T} \\
	\\
	& B
	\arrow["\sim"{description}, from=1-1, to=1-3]
	\arrow[""{name=0, anchor=center, inner sep=0}, "\pi"', from=1-1, to=3-2]
	\arrow["F", from=1-3, to=3-2]
	\arrow["\sim"{description}, shorten <=6pt, Rightarrow, from=0, to=1-3]
\end{tikzcd}\]
~~~

```agda
  πᶠ≅F : (πᶠ Antitotal) ≅ⁿ (F F∘ ∫Antitotal→)
  πᶠ≅F = iso→isoⁿ (λ (x , x' , Fx'=x) → path→iso (sym Fx'=x))
    λ {(x , x' , Fx'=x)} {(y , y' , Fy'=y)} → J₂
      (λ x y Fx'=x Fy'=y →
        ∀ ((∫hom f (f' , Ff'=f)) : ∫Hom Antitotal (x , x' , Fx'=x) (y , y' , Fy'=y))
        → F.₁ f' B.∘ path→iso (sym Fx'=x) .B.to ≡
          path→iso (sym Fy'=y) .B.to B.∘ f)
      (λ (∫hom f (f' , Ff'=f)) →
        B.elimr (transport-refl B.id) ∙∙ Ff'=f ∙∙ sym (B.eliml (transport-refl B.id)))
      Fx'=x Fy'=y
```

## Antitotal of the total

If we instead start with a [[displayed category]] $\cE \liesover \cB$,

```agda
module _ (ℰ : Displayed B o' ℓ') where
```

we would expect taking the total $\int \cE$ and then applying our
construction to the projection `πᶠ`{.Agda} to give us a displayed
category [[isomorphic|isomorphism of displayed precategories]] to $\cE$.
Indeed this is the case, although the proof gets a bit bogged down in
paths.

<!--
```agda
  open Displayed-functor

  private
    module ℰ = Dr ℰ
    module ∫ℰ = Precategory (∫ ℰ)

```
-->


  Antitotal∫→ : Vertical-functor (Antitotal (πᶠ ℰ)) ℰ
  Antitotal∫→ .F₀' ((x₂ , x') , x₂=x) = subst ℰ.Ob[_] x₂=x x'
  Antitotal∫→ .F₁' {a' = (x₂ , x') , x₂=x} {(y₂ , y') , y₂=y} (∫hom f₂ f' , f₂=f) =
    -- substd
    --   (λ {i} x → ℰ.Hom[ f₂=f i ]
    --     (transport-filler (ap ℰ.Ob[_] x₂=x) x' i)
    --     (transport-filler (ap ℰ.Ob[_] y₂=y) y' i))
    --   f₂=f f'
