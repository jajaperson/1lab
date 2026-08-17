<!--
```agda
open import Cat.Monoidal.Functor
open import Cat.Monoidal.Base
open import Cat.Functor.Naturality
open import Cat.Prelude

import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Monoidal.Functor.Naturality {oc ℓc od ℓd}
  {C : Precategory oc ℓc} {D : Precategory od ℓd}
  {Cᵐ : Monoidal-category C} {Dᵐ : Monoidal-category D}
  where
```

<!--
```agda
private
  module C where
    open Cr C public
    open Monoidal Cᵐ public
  module D where
    open Cr D public
    open Monoidal Dᵐ public
```
-->

# Naturality of monoidal functors

If $\alpha : F \iso G$ is a [[natural isomorphism]] which is [[monoidal|
monoidal natural transformation]] in one direction, it is automatically
monoidal in the other.

```agda
_≅ⁿᵐ_ : ∀ {F} {G} → Lax-monoidal-functor-on Cᵐ Dᵐ F → Lax-monoidal-functor-on Cᵐ Dᵐ G → Type (oc ⊔ ℓc ⊔ ℓd)
_≅ⁿᵐ_ {F} {G} Fᵐ Gᵐ = Σ (F ≅ⁿ G) λ α → is-monoidal-transformation Cᵐ Dᵐ Fᵐ Gᵐ (α .Isoⁿ.to)

module Isoⁿᵐ
  {F} {G} {Fᵐ : Lax-monoidal-functor-on Cᵐ Dᵐ F} {Gᵐ : Lax-monoidal-functor-on Cᵐ Dᵐ G}
  (mni : Fᵐ ≅ⁿᵐ Gᵐ)
  where
```

<!--
```agda
  private
    module F where
      open Functor F public
      open Lax-monoidal-functor-on Fᵐ public
    module G where
      open Functor G public
      open Lax-monoidal-functor-on Gᵐ public

  open Isoⁿ (mni .fst) public
  open Σ mni public using () renaming (snd to toᵐ)
  module toᵐ = is-monoidal-transformation toᵐ

  open is-monoidal-transformation
```
-->

```agda
  fromᵐ : is-monoidal-transformation Cᵐ Dᵐ Gᵐ Fᵐ from
  fromᵐ .nat-ε =
    from · C.Unit D.∘ G.ε                   ≡˘⟨ D.refl⟩∘⟨ toᵐ.nat-ε ⟩
    from · C.Unit D.∘ to · C.Unit D.∘ F.ε   ≡⟨ D.assoc _ _ _ ⟩
    (from · C.Unit D.∘ to · C.Unit) D.∘ F.ε ≡⟨ D.eliml $ ap (_· _) invr ⟩
    F.ε                                     ∎
  fromᵐ .nat-φ {x} {y} =
    from · _ D.∘ G.φ x y                                                            ≡⟨ D.refl⟩∘⟨ D.intror D.⊗.F-id ⟩
    from · _ D.∘ G.φ x y D.∘ ⌜ D.id D.⊗₁ D.id ⌝                                     ≡˘⟨ ap¡ (ap₂ D._⊗₁_ (ap (_· _) invl) (ap (_· _) invl)) ⟩
    from · _ D.∘ G.φ x y D.∘ ⌜ to · x D.∘ from · x D.⊗₁ to · y D.∘ from · y ⌝       ≡⟨ ap! $ D.⊗.F-∘ _ _ ⟩
    from · _ D.∘ G.φ x y D.∘ (to · x D.⊗₁ to · y) D.∘ (from · x D.⊗₁ from · y)      ≡⟨ cat! D ⟩
    from · _ D.∘ ⌜ G.φ x y D.∘ (to · x D.⊗₁ to · y) ⌝ D.∘ (from · x D.⊗₁ from · y)  ≡˘⟨ ap¡ toᵐ.nat-φ ⟩
    from · _ D.∘ (to · _ D.∘ F.φ x y) D.∘ (from · x D.⊗₁ from · y)                  ≡⟨ cat! D ⟩
    (from · _ D.∘ to · _) D.∘ F.φ x y D.∘ (from · x D.⊗₁ from · y)                  ≡⟨ D.eliml $ ap (_· _) invr ⟩
    F.φ x y D.∘ (from · x D.⊗₁ from · y)                                            ∎
```
