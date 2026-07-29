<!--
```agda
open import Cat.Monoidal.Functor
open import Cat.Functor.Naturality.Reflection
open import Cat.Functor.Naturality
open import Cat.Monoidal.Base
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Bifunctor
open import Cat.Prelude

open Monoidal-category
```
-->

```agda
module Cat.Monoidal.Instances.Zero where
```

## Zero monoidal category

There is a unique [[monoidal category]] structure on the [[terminal
category]] `⊤Cat`{.Agda}

```agda
⊤Catᵐ : Monoidal-category ⊤Cat
⊤Catᵐ .Unit = tt
⊤Catᵐ .-⊗- = make-bifunctor record
   { F₀ = λ _ _ → tt ; lmap = λ _ → tt ; rmap = λ _ → tt
   ; lmap-id = refl ; rmap-id = refl
   ; lmap-∘ = λ _ _ → refl ; rmap-∘ = λ _ _ → refl ; lrmap = λ _ _ → refl
   }
⊤Catᵐ .unitor-l = trivial-isoⁿ!
⊤Catᵐ .unitor-r = trivial-isoⁿ!
⊤Catᵐ .associator = trivial-isoⁿ!
⊤Catᵐ .triangle = refl
⊤Catᵐ .pentagon = refl
```
