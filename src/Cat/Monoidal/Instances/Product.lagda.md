<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Monoidal.Functor
open import Cat.Monoidal.Base
open import Cat.Prelude
open import Cat.Solver

import Cat.Reasoning as Cr

open _=>_ using (is-natural)
open Monoidal-category
```
-->

```agda
module Cat.Monoidal.Instances.Product {oc ℓc od ℓd}
  {C : Precategory oc ℓc} {D : Precategory od ℓd}
  (Cᵐ : Monoidal-category C) (Dᵐ : Monoidal-category D)
  where
```

# Product monoidal categories

<!--
```agda
private
  module C where
    open Cr C public
    open Monoidal-category Cᵐ public
  module D where
    open Cr D public
    open Monoidal-category Dᵐ public
```
-->

The product of two monoidal categories is canonically made a monoidal
category under a componentwise tensor product.

```agda
_×ᵐ_ : Monoidal-category (C ×ᶜ D)

_×ᵐ_ .-⊗- = make-bifunctor record where
  F₀ (a , x) (b , y) = a C.⊗ b , x D.⊗ y
  lmap (f , φ) = (f C.◀ _ , φ D.◀ _)
  rmap (f , φ) = (_ C.▶ f , _ D.▶ φ)
  lmap-id i = C.◀.F-id i , D.◀.F-id i
  rmap-id i = C.▶.F-id i , D.▶.F-id i
  lmap-∘ (f , φ) (g , ψ) i = C.◀.F-∘ f g i , D.◀.F-∘ φ ψ i
  rmap-∘ (f , φ) (g , ψ) i = C.▶.F-∘ f g i , D.▶.F-∘ φ ψ i
  lrmap (f , φ) (g , ψ) i = C.-⊗-.lrmap f g i , D.-⊗-.lrmap φ ψ i
  
_×ᵐ_ .Unit = C.Unit , D.Unit

_×ᵐ_ .unitor-l = to-natural-iso record where
  eta (a , x) = C.λ→ a , D.λ→ x
  inv (a , x) = C.λ← a , D.λ← x
  eta∘inv (a , x) i = C.λ≅ .C.invl i , D.λ≅ .D.invl i
  inv∘eta (a , x) i = C.λ≅ .C.invr i , D.λ≅ .D.invr i
  natural _ _ (f , g) i =
    C.unitor-l.to .is-natural _ _ f (~ i)
    , D.unitor-l.to .is-natural _ _ g (~ i)
    
_×ᵐ_ .unitor-r = to-natural-iso record where
  eta (a , x) = C.ρ→ a , D.ρ→ x
  inv (a , x) = C.ρ← a , D.ρ← x
  eta∘inv _ i = C.ρ≅ .C.invl i , D.ρ≅ .D.invl i
  inv∘eta _ i = C.ρ≅ .C.invr i , D.ρ≅ .D.invr i
  natural _ _ (f , g) i =
    C.unitor-r.to .is-natural _ _ f (~ i)
    , D.unitor-r.to .is-natural _ _ g (~ i)
    
_×ᵐ_ .associator = to-natural-iso record where
  eta ((a , x) , (b , y) , (c , z)) = C.α→ (a , b , c) , D.α→ (x , y , z)
  inv ((a , x) , (b , y) , (c , z)) = C.α← (a , b , c) , D.α← (x , y , z)
  eta∘inv _ i = C.α≅ .C.invl i , D.α≅ .D.invl i
  inv∘eta _ i = C.α≅ .C.invr i , D.α≅ .D.invr i
  natural _ _ ((f , φ) , (g , ψ) , (h , ω)) i =
    C.associator.to .is-natural _ _ (f , g , h)  (~ i)
    , D.associator.to .is-natural _ _ (φ , ψ , ω) (~ i)
    
_×ᵐ_ .triangle i = C.triangle i , D.triangle i
_×ᵐ_ .pentagon i = C.pentagon i , D.pentagon i
```

The projections `Fst`{.Agda} and `Snd`{.Agda} then become [[monoidal
functors]].

```agda
Fstᵐ : Monoidal-functor-on _×ᵐ_ Cᵐ Fst
Fstᵐ = make-monoidal-functor-on
  let
    open Make-monoidal-functor
    open Make-binatural-iso
  in λ where
    .ε → C.id-iso
    .F-mult → make-binatural-iso λ where
      .eta _ _ → C.id
      .inv _ _ → C.id
      .eta∘inv _ _ → C.id2
      .inv∘eta _ _ → C.id2
      .is-natural-◀ _ _ → sym C.id-comm
      .is-natural-▶ _ _ → sym C.id-comm
    .F-α→ →
      C.α→ _ C.∘ C.id C.∘ ⌜ C.id C.◀ _ ⌝ ≡⟨ ap! C.◀.F-id ⟩
      C.α→ _ C.∘ C.id C.∘ C.id           ≡⟨ cat! C ⟩
      C.id C.∘ ⌜ C.id ⌝ C.∘ C.α→ _       ≡˘⟨ ap¡ C.▶.F-id ⟩
      C.id C.∘ (_ C.▶ C.id) C.∘ C.α→ _   ∎
    .F-λ← → C.elimr $ C.elimr C.◀.F-id
    .F-ρ← → C.elimr $ C.elimr C.▶.F-id

Sndᵐ : Monoidal-functor-on _×ᵐ_ Dᵐ Snd
Sndᵐ = make-monoidal-functor-on
  let
    open Make-monoidal-functor
    open Make-binatural-iso
  in λ where
    .ε → D.id-iso
    .F-mult → make-binatural-iso λ where
      .eta _ _ → D.id
      .inv _ _ → D.id
      .eta∘inv _ _ → D.id2
      .inv∘eta _ _ → D.id2
      .is-natural-◀ _ _ → sym D.id-comm
      .is-natural-▶ _ _ → sym D.id-comm
    .F-α→ →
      D.α→ _ D.∘ D.id D.∘ ⌜ D.id D.◀ _ ⌝ ≡⟨ ap! D.◀.F-id ⟩
      D.α→ _ D.∘ D.id D.∘ D.id           ≡⟨ cat! D ⟩
      D.id D.∘ ⌜ D.id ⌝ D.∘ D.α→ _       ≡˘⟨ ap¡ D.▶.F-id ⟩
      D.id D.∘ (_ D.▶ D.id) D.∘ D.α→ _   ∎
    .F-λ← → D.elimr $ D.elimr D.◀.F-id
    .F-ρ← → D.elimr $ D.elimr D.▶.F-id
```
