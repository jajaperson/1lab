<!--
```agda
open import Cat.Functor.Properties
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
module Cat.Displayed.Instances.Antitotal' {o ℓ} (B : Precategory o ℓ) where
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
    module ℰᵀ = Cr ℰᵀ
    module F = Functor F
```
-->

We construct a displayed category $\cE$ where the type of objects
$\cE_x$ over $x$ is the [[essential fibre]] of $F_0$ over $x$, that is
the type of objects $x' : \cE^T$ equipped with a path $F_0 x = x'$.

```agda
  Antitotal : Displayed B (ℓ ⊔ o') (ℓ ⊔ ℓ')
  Antitotal .Ob[_] = Essential-fibre F
```
The morphisms $\cE_f((x', \alpha), (y', \beta))$ are defined similarly,
as the [[fibre]] of $F_1$ over $\beta^{-1} \circ f \circ \alpha$.

```
  Antitotal .Hom[_] f (x' , Fx'≅x) (y' , Fy'≅y) = fibre F.₁ (B.from Fy'≅y B.∘ f B.∘ B.to Fx'≅x)
  Antitotal .Hom[_]-set _ _ _ = hlevel 2
```

Identity and composition are simply those of $\cE^T$.

```agda
  Antitotal .id' {x} {x' , Fx'≅x} = ℰᵀ.id , F.F-id ∙∙ sym (B.invr Fx'≅x) ∙∙ ap (_ B.∘_) (sym (B.idl _))
  Antitotal ._∘'_ {x = x' , Fx'≅x} {y' , Fy'≅y} {z' , Fz'≅z} {f} {g} (f' , Ff'~f) (g' , Fg'~g) =
    f' ℰᵀ.∘ g' , (
      F.₁ (f' ℰᵀ.∘ g')                                                            ≡⟨ F.F-∘ _ _ ⟩
      F.₁ f' B.∘ F.₁ g'                                                           ≡⟨ Ff'~f B.⟩∘⟨ Fg'~g ⟩
      (B.from Fz'≅z B.∘ f B.∘ B.to Fy'≅y) B.∘ (B.from Fy'≅y B.∘ g B.∘ B.to Fx'≅x) ≡⟨ cat! B ⟩
      B.from Fz'≅z B.∘ (f B.∘ (B.to Fy'≅y B.∘ B.from Fy'≅y) B.∘ g) B.∘ B.to Fx'≅x ≡⟨ B.refl⟩∘⟨ (B.elim-inner (B.invl Fy'≅y) B.⟩∘⟨refl) ⟩
      B.from Fz'≅z B.∘ (f B.∘ g) B.∘ B.to Fx'≅x                                   ∎)
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
  Antitotal .hom[_] p (f' , Ff'=f) = f' , subst (λ _ → _ ≡ _) p Ff'=f
  Antitotal .coh[_] _ _ = Σ-prop-pathp! refl
```

<!--
```agda
  _ = ℰᵀ.Hom-set
```
-->

## Total of the antitotal

Taking the [[total category]] $\int \cE$ of $\cE$ gets us a precategory
which is [[equivalent|equivalence of categories]] to our orginal
category $\cE^T$.

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

  ∫Antitotal-is-equiv : is-equivalence ∫Antitotal→
  ∫Antitotal-is-equiv = ff+split-eso→is-equivalence ff eso where
    ff : is-fully-faithful ∫Antitotal→
    ff {x , x' , Fx'≅x} {y , y' , Fy'≅y} = is-iso→is-equiv $ iso
      (λ f' → ∫hom (B.to Fy'≅y B.∘ F.₁ f' B.∘ B.from Fx'≅x) (f' , B.introlr (B.invr Fy'≅y) (B.invr Fx'≅x) ∙ cat! B))
      (λ _ → refl) λ (∫hom f (f' , Ff'~f)) → ∫Hom-path Antitotal (
        B.to Fy'≅y B.∘ ⌜ F.₁ f' ⌝ B.∘ B.from Fx'≅x                            ≡⟨ ap! Ff'~f ⟩
        B.to Fy'≅y B.∘ (B.from Fy'≅y B.∘ f B.∘ B.to Fx'≅x) B.∘ B.from Fx'≅x   ≡⟨ cat! B ⟩
        (B.to Fy'≅y B.∘ B.from Fy'≅y) B.∘ f B.∘ (B.to Fx'≅x B.∘ B.from Fx'≅x) ≡⟨ B.elimlr (B.invl Fy'≅y) (B.invl Fx'≅x) ⟩
        f                                                                     ∎
      ) (Σ-prop-pathp! refl)

    eso : is-split-eso ∫Antitotal→
    eso x' = (F.₀ x' , x' , B.id-iso) , ℰᵀ.id-iso

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
  πᶠ≅F = iso→isoⁿ (λ (x , x' , Fx'≅x) → Fx'≅x B.Iso⁻¹)
    λ {(x , x' , Fx'≅x)} {(y , y' , Fy'≅y)} (∫hom f (f' , Ff'~f)) →
      F.₁ f' B.∘ B.from Fx'≅x                               ≡⟨ Ff'~f B.⟩∘⟨refl ⟩
      (B.from Fy'≅y B.∘ f B.∘ B.to Fx'≅x) B.∘ B.from Fx'≅x  ≡⟨ cat! B ⟩
      B.from Fy'≅y B.∘ f B.∘ B.to Fx'≅x B.∘ B.from Fx'≅x    ≡⟨ B.refl⟩∘⟨ B.elimr (B.invl Fx'≅x) ⟩
      B.from Fy'≅y B.∘ f                                    ∎
```

## Antitotal of the total

If we instead start with a [[displayed category]] $\cE \liesover \cB$,

```agda
module _ (ℰ : Displayed B o' ℓ') where
```

we would expect taking the total $\int \cE$ and then applying our
construction to the projection `πᶠ`{.Agda} to give us a displayed
category [[equivalent|equivalence of displayed categories]] to $\cE$.
Indeed this is the case.

```agda
  open Displayed-functor

  private
    module ℰ = Dr ℰ
    module ∫ℰ = Precategory (∫ ℰ)
```


## Eek

i have two versions of an “antitotal” construction, turning a functor into a displayed category, one which is evil and takes proper fibres, and another which uses essential fibres. the former means the total of the antitotal is _isomorphic_ to the original category, in the latter case this is just an equivalence of categories. which is preferable?
