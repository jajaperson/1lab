<!--
```agda
open import Cat.Displayed.Functor.Naturality
open import Cat.Displayed.Functor.Properties
open import Cat.Displayed.Instances.Functor
open import Cat.Displayed.Functor.Adjoint
open import Cat.Functor.Equivalence
open import Cat.Functor.Naturality
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as Dr
import Cat.Displayed.Morphism as Dm
import Cat.Reasoning as Cr

open Functor
open Displayed-functor
open _=[_]=>_
```
-->

```agda
module Cat.Displayed.Functor.Equivalence where
```

# Equivalences of displayed categories

Recall that we define an [[equivalence of categories]] is defined as a 
special kind  of [[adjoint functor]]. Similarly, if $\cE \liesover \cA$
and $\cF \liesover \cB$ are [[displayed categories]], and $F : \cA \to \cB$
is an [[equivalence|equivalence of categories]] of the [[base categories]], 
we say that a [[displayed functor]] $F' : \cE \to \cF$
over $F$ is a **displayed equivalence** over $F$ when there is a 
[[displayed adjunction]] $F' \dashv_{F \dashv F^{-1}} F'^{-1}$, 
where the the unit and counit are [[displayed natural isomorphisms]].

```agda
record is-equivalence[_] 
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B} (F-is-equiv : is-equivalence F)
  (F' : Displayed-functor F ℰ ℱ) 
  : Type (adj-level' ℰ ℱ) where

  open is-equivalence F-is-equiv public

  field
    F'⁻¹ : Displayed-functor F⁻¹ ℱ ℰ
    F'⊣'F⁻¹ : F' ⊣[ F⊣F⁻¹ ] F'⁻¹

  open _⊣[_]_ F'⊣'F⁻¹ public

  field
    unit'-iso : ∀ {x} x' →  Dm.is-invertible[_] ℰ (unit-iso x) (unit' .η' x')
    counit'-iso : ∀ {x} x' →  Dm.is-invertible[_] ℱ (counit-iso x) (counit' .η' x')
```

Again, we see that natural families of invertible morphisms give rise to
displayed isomorphisms in the [[displayed functor category]]:

<!-- 
```agda
  private
    module A = Cr A
    module B = Cr B
    module ℰ where
      open Dr ℰ public
      open Dm ℰ public
    module ℱ where
      open Dr ℱ public
      open Dm ℱ public
    [ℰ,ℰ] = DisCat[ ℰ , ℰ ]
    [ℱ,ℱ] = DisCat[ ℱ , ℱ ]
    module [ℰ,ℰ] where
      open Dr [ℰ,ℰ] public
      open Dm [ℰ,ℰ] public
    module [ℱ,ℱ] where
      open Dr [ℱ,ℱ] public
      open Dm [ℱ,ℱ] public
```
-->

```agda
  F'∘F'⁻¹≅Id' : F' F∘' F'⁻¹ [ℱ,ℱ].≅[ F∘F⁻¹≅Id ] Id'
  F'∘F'⁻¹≅Id' = [ℱ,ℱ].invertible[]→iso[]
   (invertible[]→invertibleⁿ[ _ ] counit' counit'-iso)
  
  Id'≅F'⁻¹∘'F' : Id' [ℰ,ℰ].≅[ Id≅F⁻¹∘F ] F'⁻¹ F∘' F'
  Id'≅F'⁻¹∘'F' = [ℰ,ℰ].invertible[]→iso[]
    (invertible[]→invertibleⁿ[ _ ] unit' unit'-iso)

  unit'⁻¹ = [ℰ,ℰ].from' Id'≅F'⁻¹∘'F'
  counit'⁻¹ = [ℱ,ℱ].from' F'∘F'⁻¹≅Id'
```

This implies the displayed adjunction

```agda
  F'⁻¹⊣F' : F'⁻¹ ⊣[ F⁻¹⊣F ] F'
```

whence we have

```agda
  inverse-equivalence' : is-equivalence[ inverse-equivalence ] F'⁻¹
```

<details>
<summary>Construction of `F'⁻¹⊣F'`{.Agda} and `inverse-equivalence'`{.Agda}</summary>
```agda
  F'⁻¹⊣F' ._⊣[_]_.unit' = counit'⁻¹
  F'⁻¹⊣F' ._⊣[_]_.counit' = unit'⁻¹
  F'⁻¹⊣F' ._⊣[_]_.zig' {b} {b'} = z' where
    z' : unit'⁻¹ .η' (₀' F'⁻¹ b') ℰ.∘' ₁' F'⁻¹ (counit'⁻¹ .η' b') 
      ℰ.≡[ _⊣_.zig F⁻¹⊣F ] ℰ.id'
    z' = ℰ.cast[] $ ℰ.inverse-unique₀' 
      ((F'-map-iso F'⁻¹ (isoⁿ[]→iso[] F'∘F'⁻¹≅Id' b')) 
        ℰ.∘Iso' isoⁿ[]→iso[] Id'≅F'⁻¹∘'F' (₀' F'⁻¹ b')) 
      ℰ.id-iso↓ zag'
  F'⁻¹⊣F' ._⊣[_]_.zag' {a} {a'} = z' where
    z' : ₁' F' (unit'⁻¹ .η' a') ℱ.∘' counit'⁻¹ .η' (₀' F' a') 
      ℱ.≡[ _⊣_.zag F⁻¹⊣F ] ℱ.id'
    z' = ℱ.cast[] $ ℱ.inverse-unique₀' 
      (isoⁿ[]→iso[] F'∘F'⁻¹≅Id' (₀' F' a') 
        ℱ.∘Iso' F'-map-iso F' (isoⁿ[]→iso[] Id'≅F'⁻¹∘'F' a')) 
      ℱ.id-iso↓ zig'

  inverse-equivalence' = record 
    { F'⁻¹ = F' 
    ; F'⊣'F⁻¹ = F'⁻¹⊣F'
    ; unit'-iso = λ x' → ℱ.is-invertible[]-inverse (counit'-iso x') 
    ; counit'-iso = λ x' → ℰ.is-invertible[]-inverse (unit'-iso x') }
```
</details>

As with an ordinary [[equivalence of categories]] there are other ways
of characterising displayed equivalences which will usually be more
convenient when it comes to constructing equivalences by hand.

## Fully faithful, essentially surjective

```agda
module _
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B} {F' : Displayed-functor F ℰ ℱ}
  (ff : is-fully-faithful F) (eso : is-split-eso F) 
  (ff' : is-ff' F') (eso' : is-split-eso[ eso ] F')
  where
```

<!--
```agda
  private
    module A where
      open Cr A public
      open _≅_ public
    module B where
      open Cr B public
      open _≅_ public
    module ℰ where
      open Dr ℰ public
      open Dm ℰ public
    module ℱ where
      open Dr ℱ public
      open Dm ℱ public

    G = ff+split-eso→inverse {F = F} ff eso

    ff⁻¹ : ∀ {x y} → B.Hom (₀ F x) (₀ F y) → A.Hom _ _
    ff⁻¹ = equiv→inverse ff
    module ff {x} {y} = Equiv (_ , ff {x} {y})
    
    ff'⁻¹ 
      : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} 
      → ℱ.Hom[ f ] (₀' F' x') (₀' F' y') 
      → ℰ.Hom[ ff⁻¹ f ] x' y'
    ff'⁻¹ {f = f} f' = equiv→inverse ff' $ ℱ.hom[ sym (ff.ε f) ] f'
    module ff' where
      module _ {x} {y} {f} {x'} {y'} where 
        open Equiv (_ , ff' {x} {y} {f} {x'} {y'}) public
      -- We need “displayed” versions of the unit and counit to account
      -- for transport.
      ε[]
        : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} 
          (f' : ℱ.Hom[ f ] (₀' F' x') (₀' F' y'))
        → ₁' F' (ff'⁻¹ f') ℱ.≡[ ff.ε f ] f'
      ε[] {f = f} f' = ℱ.cast[] $
        ₁' F' (equiv→inverse ff' (ℱ.hom[ sym (ff.ε f) ] f')) ℱ.≡[]⟨ ε (ℱ.hom[ sym (ff.ε f) ] f') ⟩
        ℱ.hom[ sym (ff.ε f) ] f' ℱ.≡[]˘⟨ ℱ.coh[ sym (ff.ε f) ] f' ⟩
        f' ∎

      η[]
        : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} (f' : ℰ.Hom[ f ] x' y')
        → ff'⁻¹ (₁' F' f') ℰ.≡[ ff.η f ] f'
      η[] {f = f} f' = ℰ.cast[] $
        equiv→inverse (ff' {f = ff .is-eqv (₁ F f) .centre .fst}) (ℱ.hom[ sym (ff.ε (₁ F f)) ] (₁' F' f'))  ℰ.≡[]⟨ apd (λ _ → equiv→inverse ff') (ℱ.coh[ ap (₁ F) (ff.η f) ] (ℱ.hom[ sym (ff.ε (₁ F f)) ] (₁' F' f'))) ⟩
        equiv→inverse (ff' {f = f}) (ℱ.hom[ ap (₁ F) (ff.η f) ] (ℱ.hom[ sym (ff.ε (₁ F f)) ] (₁' F' f')))   ℰ.≡[]⟨ apd (λ _ → equiv→inverse (ff' {f = f})) (ℱ.hom[]-∙ (sym (ff.ε (₁ F f))) (ap (₁ F) (ff.η f))) ⟩
        equiv→inverse (ff' {f = f}) (ℱ.hom[ sym (ff.ε (₁ F f)) ∙ ap (₁ F) (ff.η f) ] (₁' F' f'))            ℰ.≡[]˘⟨ apd (λ _ → equiv→inverse (ff' {f = f})) (ℱ.cast[] $ ℱ.coh[ sym (ff.ε (₁ F f)) ∙ ap (₁ F) (ff.η f) ]  (₁' F' f')) ⟩
        equiv→inverse (ff' {f = f}) (₁' F' f')                                                              ℰ.≡[]⟨ η f' ⟩
        f'                                                                                                  ∎
```
-->

```agda
  ff[_]+split-eso[_]→inverse[] : Displayed-functor G ℱ ℰ
  ff[_]+split-eso[_]→inverse[] .F₀' {b} b' = eso' b' .fst
  ff[_]+split-eso[_]→inverse[] .F₁' {x} {y} {f} {x'} {y'} f' = 
    ff'⁻¹ (f*y'-iso .ℱ.from' ℱ.∘' f' ℱ.∘' f*x'-iso .ℱ.to')
    where
      open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
      open Σ (eso' y') renaming (fst to f*y' ; snd to f*y'-iso)
  
  ff[_]+split-eso[_]→inverse[] .F-id' {x} {x'} = 
    ff'⁻¹ (f*x'-iso .ℱ.from' ℱ.∘' ℱ.id' ℱ.∘' f*x'-iso .ℱ.to') ℰ.≡[]⟨ apd (λ _ f' → ff'⁻¹ (f*x'-iso .ℱ.from' ℱ.∘' f')) (ℱ.idl' (f*x'-iso .ℱ.to')) ⟩
    ff'⁻¹ (f*x'-iso .ℱ.from' ℱ.∘' f*x'-iso .ℱ.to')            ℰ.≡[]⟨ apd (λ _ → ff'⁻¹) (f*x'-iso .ℱ.inverses' .ℱ.Inverses[_].invr') ⟩
    ff'⁻¹ ℱ.id'                                               ℰ.≡[]˘⟨ apd (λ _ → ff'⁻¹) (F' .F-id') ⟩
    ff'⁻¹ (₁' F' ℰ.id')                                       ℰ.≡[]⟨ ff'.η[] ℰ.id' ⟩
    ℰ.id'                                                     ∎
    where
      open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)

  ff[_]+split-eso[_]→inverse[] .F-∘' {x} {y} {z} {f} {g} {x'} {y'} {z'} {f'} {g'} = ff'→faithful' ff' $ ℱ.cast[] $
    ₁' F' (ff'⁻¹ (ffz' ℱ.∘' (f' ℱ.∘' g') ℱ.∘' ftx'))                                  ℱ.≡[]⟨ ff'.ε[] (ffz' ℱ.∘' (f' ℱ.∘' g') ℱ.∘' ftx') ⟩
    ffz' ℱ.∘' (f' ℱ.∘' g') ℱ.∘' ftx'                                                  ℱ.≡[]˘⟨ apd (λ _ → ffz' ℱ.∘'_) (ℱ.assoc' f' g' ftx') ⟩
    ffz' ℱ.∘' f' ℱ.∘' g' ℱ.∘' ftx'                                                    ℱ.≡[]˘⟨ apd (λ _ h' → ffz' ℱ.∘' f' ℱ.∘' h') (ℱ.idl' (g' ℱ.∘' ftx')) ⟩
    ffz' ℱ.∘' f' ℱ.∘' ℱ.id' ℱ.∘' g' ℱ.∘' ftx'                                         ℱ.≡[]˘⟨ apd (λ _ h' → ffz' ℱ.∘' f' ℱ.∘' h' ℱ.∘' g' ℱ.∘' ftx')  (f*y'-iso .ℱ.invl') ⟩
    ffz' ℱ.∘' f' ℱ.∘' (fty' ℱ.∘' ffy') ℱ.∘' g' ℱ.∘' ftx'                              ℱ.≡[]˘⟨ apd (λ _ h' → ffz' ℱ.∘' f' ℱ.∘' h') (ℱ.assoc' fty' ffy' (g' ℱ.∘' ftx')) ⟩
    ffz' ℱ.∘' f' ℱ.∘' fty' ℱ.∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')                              ℱ.≡[]⟨ apd (λ _ → ffz' ℱ.∘'_) (ℱ.assoc' f' fty' (ffy' ℱ.∘' g' ℱ.∘' ftx'))⟩
    ffz' ℱ.∘' (f' ℱ.∘' fty') ℱ.∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')                            ℱ.≡[]⟨ ℱ.assoc' ffz' (f' ℱ.∘' fty') (ffy' ℱ.∘' g' ℱ.∘' ftx') ⟩
    (ffz' ℱ.∘' f' ℱ.∘' fty') ℱ.∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')                            ℱ.≡[]˘⟨ apd (λ _ → ℱ._∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')) (ff'.ε[] (ffz' ℱ.∘' f' ℱ.∘' fty')) ⟩
    ₁' F' (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty')) ℱ.∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')               ℱ.≡[]˘⟨ apd (λ _ → ₁' F' (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty')) ℱ.∘'_) (ff'.ε[] (ffy' ℱ.∘' g' ℱ.∘' ftx')) ⟩
    ₁' F' (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty')) ℱ.∘' ₁' F' (ff'⁻¹ (ffy' ℱ.∘' g' ℱ.∘' ftx')) ℱ.≡[]˘⟨ F' .F-∘' {f' = (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty'))} {g' = (ff'⁻¹ (ffy' ℱ.∘' g' ℱ.∘' ftx'))}⟩
    ₁' F' (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty') ℰ.∘' ff'⁻¹ (ffy' ℱ.∘' g' ℱ.∘' ftx'))        ∎
    where
      open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
      open Σ (eso' y') renaming (fst to f*y' ; snd to f*y'-iso)
      open Σ (eso' z') renaming (fst to f*z' ; snd to f*z'-iso)

      ffz' = f*z'-iso .ℱ.from'
      ffy' = f*y'-iso .ℱ.from'
      ftz' = f*z'-iso .ℱ.to'
      fty' = f*y'-iso .ℱ.to'
      ffx' = f*x'-iso .ℱ.from'
      ftx' = f*x'-iso .ℱ.to'
```




## Isomorphisms of displayed precategories {defines="isomorphism-of-displayed-precategories"}

If $F'$ is displayed over an [[isomorphism of precategories]] $F$, we
can prove that $F'$ is a displayed equivalence by showing that it is an
**isomorphism of displayed precategories**: It is componentwise an 
isomorphism on objects and morphisms.

```agda
record is-precat-iso[_] 
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B} (F-is-iso : is-precat-iso F) (F' : Displayed-functor F ℰ ℱ)
  : Type (adj-level' ℰ ℱ)
  where
    no-eta-equality
    constructor iso'
    field
      has-is-ff' : ∀ {a b} {f} {a' : Dr.Ob[_] ℰ a} {b' : Dr.Ob[_] ℰ b}
        →  is-equiv {A = Dr.Hom[_] ℰ f a' b'} (F' .F₁')
      has-is-iso' : ∀ a → is-equiv {A = Dr.Ob[_] ℰ a} (F' .F₀')
```
