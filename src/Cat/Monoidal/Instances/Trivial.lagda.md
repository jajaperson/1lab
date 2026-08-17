<!--
```agda
open import Cat.Functor.Naturality.Reflection
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Monoidal.Functor
open import Cat.Monoidal.Base
open import Cat.Univalent
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
  !Fᵐ = make-monoidal-functor-on record
    { ε = ⊤C.id-iso
    ; F-mult = make-binatural-iso record
      { eta = λ _ _ → tt ; inv = λ _ _ → tt
      ; eta∘inv = λ _ _ → refl ; inv∘eta = λ _ _ → refl
      ; is-natural-◀ = λ _ _ → refl ; is-natural-▶ = λ _ _ → refl
      }
    ; F-α→ = refl ; F-λ← = refl ; F-ρ← = refl
    }

  !Fˡ = Monoidal-functor-on.lax !Fᵐ
```

On the other hand, the `constant functor`{.Agda ident="!Const"} at the
unit of $\cC$ is also monoidal.

```agda
  ¡Fᵐ : Monoidal-functor-on ⊤ᵐ Cᵐ (!Const C.Unit)
  ¡Fᵐ = make-monoidal-functor-on record
    { ε = C.id-iso
    ; F-mult =  make-binatural-iso record
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

  ¡Fˡ = Monoidal-functor-on.lax ¡Fᵐ
```

In fact, the trivial monoidal category is characterized by a universal
property analogous to that of a [[zero object]]. Stating this in full
would require a detour into bicategory theory, for now we just
construct the monoidal natural transformations involved.

```agda
  !Fˡ<=ᵐ
    : ∀ {F} (Fˡ : Lax-monoidal-functor-on Cᵐ ⊤ᵐ F)
    → is-monoidal-transformation Fˡ !Fˡ (path→iso !F-unique .Isoⁿ.to)
  !Fˡ<=ᵐ _ = record { nat-ε = refl ; nat-φ = refl }

  ¡Fˡ=>ᵐ
    : ∀ {F} (Fˡ : Lax-monoidal-functor-on ⊤ᵐ Cᵐ F)
    → let module Fˡ = Lax-monoidal-functor-on Fˡ
      in is-monoidal-transformation ¡Fˡ Fˡ (!constⁿ Fˡ.ε)
  ¡Fˡ=>ᵐ {F} Fˡ = record where
    open Lax-monoidal-functor-on Fˡ
    open Functor F
    nat-ε = C.idr _
    nat-φ =
      ε C.∘ C.λ← C.Unit                                            ≡˘⟨ C.unitor-l.from ._=>_.is-natural _ _ _ ⟩
      C.λ← (F₀ tt) C.∘ (C.Unit C.▶ ε)                              ≡˘⟨ F-λ← C.⟩∘⟨refl ⟩
      (⌜ F₁ tt ⌝ C.∘ φ tt tt C.∘ (ε C.◀ F₀ tt)) C.∘ (C.Unit C.▶ ε) ≡⟨ ap! F-id ⟩
      (C.id C.∘ φ tt tt C.∘ (ε C.◀ F₀ tt)) C.∘ (C.Unit C.▶ ε)      ≡⟨ cat! C ⟩
      φ tt tt C.∘ ((ε C.◀ F₀ tt) C.∘ (C.Unit C.▶ ε))               ≡⟨⟩
      φ tt tt C.∘ (ε C.⊗₁ ε)                                       ∎
```

Note that `!Fˡ<=ᵐ`{.Agda} gives a [[monoidal natural isomorphism]] even
when the monoidal functor being compared is lax. On the other hand,
`¡F=>ᵐ`{.Agda}, being the constant natural transformation arising from
$\epsilon : 1 \to F \rm{tt}$, is only an isomorphism if $\epsilon$ is
invertible.
