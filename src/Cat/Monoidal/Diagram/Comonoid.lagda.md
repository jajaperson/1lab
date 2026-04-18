<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import Cat.Monoidal.Instances.Cartesian
open import Cat.Displayed.Univalence.Thin
open import Cat.Monoidal.Diagram.Monoid
open import Cat.Displayed.Functor
open import Cat.Bi.Diagram.Monad
open import Cat.Monoidal.Functor
open import Cat.Displayed.Base
open import Cat.Displayed.Path
open import Cat.Monoidal.Base
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Diagram.Monad as Mo
import Cat.Reasoning
```
-->

```agda
module Cat.Monoidal.Diagram.Comonoid where
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (Cᵐ : Monoidal-category C) where
  private module C where
    open Cat.Reasoning C public
    open Monoidal-category Cᵐ public
```
-->

# Comonoids in a monoidal category {defines="comonoid-object"}

A **comonoid** in a [monoidal category] is the dual concept of a [monoid],
similarly consisting of diagrams in $\cC$ centred around an object $M$,
the comonoid itself.

Instead of a unit we have a "counit" map $\epsilon : M \to 1$ and
"comultiplication" map $\Delta : M \to M \otimes M$. The intuition is
that $\epsilon$ describes a way to destroy data and $\Delta$ describes a
way to duplicate data. Again, these maps should be compatible with the
unitors and associator of the underlying monoidal category:

[monoidal category]: Cat.Monoidal.Base.html#monoidal-categories
[monoid]: Cat.Monoidal.Diagram.Monoid.html

```agda
  record Comonoid-on (M : C.Ob) : Type ℓ where
    no-eta-equality
    field
      ε : C.Hom M C.Unit
      Δ : C.Hom M (M C.⊗ M)

      Δ-counitl : (ε C.◀ _) C.∘ Δ ≡ C.λ→ _
      Δ-counitr : (_ C.▶ ε) C.∘ Δ ≡ C.ρ→ _
      Δ-coassoc : (_ C.▶ Δ) C.∘ Δ ≡ C.α→ _ C.∘ (Δ C.◀ _) C.∘ Δ
```

## The category Comon(C)

Just as with [monoids], the comonoid objects in $\cC$ can be made into a
category, which we define here as a category $\rm{Comon}(\cC) \liesover \cC$
[[displayed over|displayed category]] $\cC$.

[monoids]: Cat.Monoidal.Diagram.Monoid.html

<!--
```agda
_ = is-monoid-hom

module _ {o ℓ} {C : Precategory o ℓ} (Cᵐ : Monoidal-category C) where
  private module C where
    open Cat.Reasoning C public
    open Monoidal-category Cᵐ public
```
-->

This means constructing a predicate on maps $f : m \to n$ expressing the
condition of being a comonoid homomorphism, which is dual to
`is-monoid-hom`{.Agda}.

```agda
  record
    is-comonoid-hom {m n} (f : C.Hom m n)
     (mo : Comonoid-on Cᵐ m) (no : Comonoid-on Cᵐ n) : Type ℓ where

    private
      module m = Comonoid-on mo
      module n = Comonoid-on no

    field
      pres-ε : n.ε C.∘ f ≡ m.ε
      pres-Δ : n.Δ C.∘ f ≡ (f C.⊗₁ f) C.∘ m.Δ
```

Again, we see that being a comonoid homomorphism is a pair of propositions
and thus is itself a proposition, greatly simplifying the construction of
the displayed category.

<!--
```agda
  private
    unquoteDecl eqv = declare-record-iso eqv (quote is-comonoid-hom)

    instance
      H-Level-is-comonoid-hom : ∀ {m n} {f : C .Precategory.Hom m n} {mo no} {k}
        → H-Level (is-comonoid-hom f mo no) (suc k)
      H-Level-is-comonoid-hom = prop-instance $ Iso→is-hlevel! 1 eqv

  open Displayed
  open Functor
  open is-comonoid-hom
```
-->

```agda
  Comon[_] : Displayed C ℓ ℓ
  Comon[_] = with-thin-display record where
    Ob[_] = (Comonoid-on Cᵐ)
    Hom[_] = is-comonoid-hom

    id' = record where
      pres-ε = C.idr _
      pres-Δ = C.idr _ ∙ C.introl C.⊗.F-id

    _∘'_ {x = x} {y} {z} {f} {g} fh gh = record where
      pres-ε = C.pulll (fh .pres-ε) ∙ gh .pres-ε
      pres-Δ =
        z .Comonoid-on.Δ C.∘ f C.∘ g                    ≡⟨ C.extendl (fh .pres-Δ) ⟩
        (f C.⊗₁ f) C.∘ y .Comonoid-on.Δ C.∘ g           ≡⟨ (C.refl⟩∘⟨ gh .pres-Δ) ⟩
        (f C.⊗₁ f) C.∘ (g C.⊗₁ g) C.∘ x .Comonoid-on.Δ  ≡˘⟨ C.pushl (C.⊗.F-∘ _ _) ⟩
        (f C.∘ g C.⊗₁ f C.∘ g) C.∘ x .Comonoid-on.Δ     ∎
```
