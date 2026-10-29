<!--
```agda
open import Cat.Prelude

open import Data.Apartness

import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Instances.Asets (ℓ ℓ# : Level) where
```

# Category of asets {.defines="category-of-asets"}

[[Asets]] and [[strongly extensional functions]] assemble into a
category.

```agda
open Precategory

Asets : Precategory (lsuc ℓ ⊔ lsuc ℓ#) (ℓ ⊔ ℓ#)
Asets .Ob = Σ (Type ℓ) λ A → Tight-apartness A ℓ#
Asets .Hom A B = Σ (⌞ A ⌟ → ⌞ B ⌟) λ f → is-strongly-ext (A .snd) (B .snd) f
Asets .Hom-set A B =
  let
    module B = Tight-apartness (B .snd)
    instance
      H-Level-B : ∀ {n} → H-Level ⌞ B ⌟ (2 + n)
      H-Level-B = basic-instance 2 B.has-is-set
  in hlevel 2
Asets .id = (λ x → x) , λ x#y → x#y
Asets ._∘_ (f , fˢˣ) (g , gˢˣ) = f ⊙ g , gˢˣ ⊙ fˢˣ
Asets .idl _ = Σ-path refl prop!
Asets .idr _ = Σ-path refl prop!
Asets .assoc _ _ _ = Σ-path refl prop!
```

<!--
```agda
open Cr Asets
```
-->

With a little effort, we can show that `Asets`{.Agda} is indeed a
[[univalent category]]

```
Asets-is-category : is-category Asets
Asets-is-category .to-path {A} {B} h = Σ-pathp S R where
  module A = Tight-apartness (A .snd)
  module B = Tight-apartness (B .snd)

  S : ⌞ A ⌟ ≡ ⌞ B ⌟
  S = ua λ where
    .fst → h .to .fst
    .snd → is-iso→is-equiv $
      iso (h .from .fst) (happly $ ap fst $ h .invl) (happly $ ap fst $ h .invr)

  S-is-set : (i : I) → is-set (S i)
  S-is-set i = coe0→i (λ i → is-set (S i)) i A.has-is-set

  h#-is-equiv : ∀ {x y} → is-equiv (h .to .snd {x} {y})
  h#-is-equiv {x} {y} = biimp-is-equiv (hlevel 1) (hlevel 1) (h .to .snd) $
    subst (λ f → (f x) A.# (f y) → h · x B.# h · y) (ap fst (h .invr))
    (h .from .snd {h · x} {h · y})

  open Tight-apartness using (apartness ; tight ; has-is-set)
  open Apartness

  R : PathP (λ i → Tight-apartness (S i) ℓ#) (A .snd) (B .snd)
  R i .apartness ._#_ x y = Glue ((unglue x) B.# (unglue y)) λ where
    (i = i0) → (x A.# y) , _ , inverse-is-equiv h#-is-equiv
    (i = i1) → (x B.# y) , _ , id-equiv
  R i .apartness .has-is-apartness = is-prop→pathp
    {B = λ i → is-apartness (R i .apartness ._#_)}
    (λ _ → hlevel 1) A.has-is-apartness B.has-is-apartness i
  R i .tight = is-prop→pathp
    {B = λ i → is-tight (R i .apartness ._#_)}
    (λ i →
      let instance
        H-Level-Si : ∀ {n} → H-Level (S i) (2 + n)
        H-Level-Si = basic-instance 2 (S-is-set i)
      in hlevel 1)
    A.tight B.tight i
Asets-is-category .to-path-over {A} {B} h = ≅-pathp _ _ $
  Σ-prop-pathp (λ _ _ → hlevel 1) (funextP λ a → path→ua-pathp _ refl)
```

Since an aset is automatically a set, there is a forgetful functor into
`Sets`{.Agda}

```agda
open Functor

πᶠ : Functor Asets (Sets ℓ)
πᶠ .F₀ A = el ⌞ A ⌟ (Tight-apartness.has-is-set (A .snd))
πᶠ .F₁ = fst
πᶠ .F-id = refl
πᶠ .F-∘ _ _ = refl
```
