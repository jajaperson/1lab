<!--
```agda
open import Cat.Functor.Naturality.Reflection
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Monoidal.Functor
open import Cat.Monoidal.Base
open import Cat.Prelude

import Cat.Reasoning as Cr

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

Let $\cC$ be a monoidal category. The unique functor `!F`{.Agda} is a
[[monoidal functor]].

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {Cᵐ : Monoidal-category C} where
  private
    module ⊤C where
      open Cr ⊤Cat public
      open Monoidal ⊤ᵐ public
    module C where
      open Cr C public
      open Monoidal Cᵐ public
```
-->

```agda
  !Fᵐ : Monoidal-functor-on Cᵐ ⊤ᵐ !F
  !Fᵐ = make-monoidal-functor-on $ record
    { ε = ⊤C.id-iso
    ; F-mult = make-binatural-iso $ record
      { eta = λ _ _ → tt ; inv = λ _ _ → tt
      ; eta∘inv = λ _ _ → refl ; inv∘eta = λ _ _ → refl
      ; is-natural-◀ = λ _ _ → refl ; is-natural-▶ = λ _ _ → refl
      }
    ; F-α→ = refl ; F-λ← = refl ; F-ρ← = refl
    }
```

On the other hand, the `constant functor`{.Agda ident="!Const"} at the
unit of $\cC$ is also monoidal.

```agda
  ¡Fᵐ : Monoidal-functor-on ⊤ᵐ Cᵐ (!Const C.Unit)
  ¡Fᵐ = make-monoidal-functor-on $ record
    { ε = C.id-iso
    ; F-mult =  make-binatural-iso $ record
      { eta = λ _ _ → C.λ← C.Unit
      ; inv = λ _ _ → C.λ→ C.Unit
      ; eta∘inv = λ _ _ → C.λ≅ .C.invr
      ; inv∘eta = λ _ _ → C.λ≅ .C.invl
      ; is-natural-◀ = λ _ _ → C.elimr C.◀.F-id ∙ sym (C.idl _)
      ; is-natural-▶ = λ _ _ → C.elimr C.▶.F-id ∙ sym (C.idl _)
      }
    ; F-α→ = C.idl _ ∙ ap (C.λ← C.Unit C.∘_) (sym $
        (C.Unit C.▶ C.λ← C.Unit) C.∘ C.α→ _ ≡⟨ C.triangle-α→ ⟩
        ⌜ C.ρ← C.Unit ⌝ C.◀ C.Unit          ≡˘⟨ ap¡ C.λ≡ρ ⟩
        C.λ← C.Unit C.◀ C.Unit              ∎
        )
    ; F-λ← = C.idl _ ∙ C.elimr C.◀.F-id
    ; F-ρ← = C.idl _ ∙∙ C.elimr C.▶.F-id ∙∙ C.λ≡ρ
    }
```

In fact, the trivial monoidal category is characterized by a universal
property analogous to that of a [[zero object]]. The monoidal functor
`!Fᵐ`{.Agda} is unique up to monoidal natural isomorphism.
