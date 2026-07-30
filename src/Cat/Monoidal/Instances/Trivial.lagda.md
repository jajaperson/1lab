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
module Cat.Monoidal.Instances.Trivial where
```

## Trivial monoidal category

There is a unique [[monoidal category]] structure on the [[terminal
category]] `⊤Cat`{.Agda}

```agda
⊤ᵐ : Monoidal-category ⊤Cat
⊤ᵐ .Unit = tt
⊤ᵐ .-⊗- = make-bifunctor record
   { F₀ = λ _ _ → tt ; lmap = λ _ → tt ; rmap = λ _ → tt
   ; lmap-id = refl ; rmap-id = refl
   ; lmap-∘ = λ _ _ → refl ; rmap-∘ = λ _ _ → refl ; lrmap = λ _ _ → refl
   }
⊤ᵐ .unitor-l = trivial-isoⁿ!
⊤ᵐ .unitor-r = trivial-isoⁿ!
⊤ᵐ .associator = trivial-isoⁿ!
⊤ᵐ .triangle = refl
⊤ᵐ .pentagon = refl
```
