<!--
```agda
open import Cat.Functor.Naturality.Reflection
open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Hom.Representable hiding (module Corep)
open import Cat.Functor.Naturality
open import Cat.Functor.Properties
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Instances.Sets
open import Cat.Functor.Hom
open import Cat.Reasoning as Cr
open import Cat.Prelude

open Functor
```
-->

```agda
module Cat.Concrete where
```

# Concrete categories {defines="concrete-category representably-concrete-category"}

A **representably concrete category** is a [locally $\kappa$-small][univ]
category $\cC$ equipped with a [[corepresentable|corepresentable functor]]
[[faithful functor]] $U : \cC \mono \Sets_{\kappa}$.

[univ]: 1Lab.intro.html#universes-and-size-issues

<!--
```agda
private variable
  o ℓ : Level
  C D : Precategory o ℓ
```
-->

```agda
record Representably-concrete (C : Precategory o ℓ) : Type (o ⊔ lsuc ℓ) where
  private module C = Cr C

  field
    U               : Functor C (Sets ℓ)
    has-is-faithful : is-faithful U
    has-corep       : Corepresentation U
```

An immediate consequence of this is that the corepresenting object
`corep`{.Agda} of $U$ is a _separator_: Generalized elements with domain
`corep`{.Agda} are enough to distinguish morphisms in $C$.

```agda
  open Corepresentation has-corep public

  corep-is-separator
    : ∀ {X Y} (f g : C.Hom X Y)
    → (∀ (x : C.Hom corep X) → f C.∘ x ≡ g C.∘ x)
    → f ≡ g
  corep-is-separator f g p = has-is-faithful $ substⁿ-≡ (corepresents ni⁻¹) $ funext p
```

The canonical example of a representably concrete category is
$\Sets_\kappa$ itself. Since elements of a set are equivalent to maps
from a singleton, the identity functor on $\Sets_\kappa$ is represented
by its terminal object `⊤'`{.Agda}.

```agda  
Sets-is-representably-concrete : Representably-concrete (Sets ℓ)
Sets-is-representably-concrete {ℓ} =
  let
    ⊤' : Set ℓ
    ⊤' = el! $ Lift ℓ ⊤
 
    X≃⊤→X : ∀ {X : Type ℓ} → X ≃ (⌞ ⊤' ⌟ → X)
    X≃⊤→X = (λ x _ → x) , is-iso→is-equiv (iso (λ f → f _) (λ _ → refl) λ _ → refl)

    Id≅Hom⊤ : Id ≅ⁿ Hom-from (Sets ℓ) ⊤'
    Id≅Hom⊤ = iso→isoⁿ (λ _ → equiv→iso X≃⊤→X) λ f → funext λ x → refl
  in record
    { U = Id
    ; has-is-faithful = λ p → p
    ; has-corep = record
      { corep = ⊤'
      ; corepresents = Id≅Hom⊤
      }
    }
```

More generally, a faithful functor $U : \cC \to \Sets_\kappa$ makes
$\cC$ representably concrete whenever `⊤'`{.Agda} has a [[free object]]
$\top^*$ in $\cC$: The `fold`{.Agda ident="fold-equiv"} operation gives
an equivalence $\cC(\top^*, X) \simeq \Sets(\top, U(X))$, which in turn
is equivalent to the set $U(X)$.

<!--
```agda
-- Needs to be here to prevent instance overlap
private
  U≅Id∘U : ∀ {U : Functor C D} → U ≅ⁿ Id F∘ U
  U≅Id∘U = trivial-isoⁿ!
```
-->

```agda
module _ {C : Precategory o ℓ} {U : Functor C (Sets ℓ)} where
  free-⊤→corepresentation : Free-object U (el! (Lift ℓ ⊤)) → Corepresentation U
  free-⊤→corepresentation free-⊤ = record where
```

<--
```agda
    module C = Cr C
    open Representably-concrete (Sets-is-representably-concrete {ℓ}) using () renaming (corep to ⊤' ; corepresents to Id≅Hom⊤)
```
-->

```agda
    open Free-object free-⊤ renaming (free to corep)

    φ : Hom-from (Sets ℓ) ⊤' F∘ U ≅ⁿ Hom-from C corep
    φ = iso→isoⁿ (λ X → equiv→iso fold-equiv)
      λ f → funext λ g → sym $ fold-natural f g

    corepresents = φ ∘ni (Id≅Hom⊤ ◂ni U) ∘ni U≅Id∘U

  faithful→free-⊤→representably-concrete
    : is-faithful U → Free-object U (el! (Lift ℓ ⊤))
    → Representably-concrete C
  faithful→free-⊤→representably-concrete p free-⊤ = record
    { U = U
    ; has-is-faithful = p
    ; has-corep = free-⊤→corepresentation free-⊤
    }
```


