<!--
```agda
open import Cat.Displayed.Functor.Naturality
open import Cat.Displayed.Functor.Properties
open import Cat.Displayed.Instances.Functor
open import Cat.Displayed.Functor.Adjoint
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as Dr
import Cat.Displayed.Morphism as Dm
import Cat.Reasoning as Cr

open Displayed-functor
open _=[_]=>_
```
-->


```agda
module Cat.Displayed.Functor.Equivalence where
```

# Equivalences of displayed categories {defines="displayed-equivalence"}

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
    F'⊣F'⁻¹ : F' ⊣[ F⊣F⁻¹ ] F'⁻¹

  open _⊣[_]_ F'⊣F'⁻¹ public

  field
    unit'-iso : ∀ {x} x' →  Dm.is-invertible[_] ℰ (unit-iso x) (unit' .η' x')
    counit'-iso : ∀ {x} x' →  Dm.is-invertible[_] ℱ (counit-iso x) (counit' .η' x')
```

Again, we see that natural families of invertible morphisms give rise to
displayed isomorphisms in the [[displayed functor category]]:

<!-- 
```agda
  private
    module F = Functor F
    module F⁻¹ = Functor F⁻¹
    module F' = Displayed-functor F'
    module F'⁻¹ = Displayed-functor F'⁻¹
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
    z' : unit'⁻¹ .η' (F'⁻¹.₀' b') ℰ.∘' F'⁻¹.₁' (counit'⁻¹ .η' b') 
      ℰ.≡[ _⊣_.zig F⁻¹⊣F ] ℰ.id'
    z' = ℰ.cast[] $ ℰ.inverse-unique₀' 
      ((F'-map-iso F'⁻¹ (isoⁿ[]→iso[] F'∘F'⁻¹≅Id' b')) 
        ℰ.∘Iso' isoⁿ[]→iso[] Id'≅F'⁻¹∘'F' (F'⁻¹.₀' b')) 
      ℰ.id-iso↓ zag'
  F'⁻¹⊣F' ._⊣[_]_.zag' {a} {a'} = z' where
    z' : F'.₁' (unit'⁻¹ .η' a') ℱ.∘' counit'⁻¹ .η' (F'.₀' a') 
      ℱ.≡[ _⊣_.zag F⁻¹⊣F ] ℱ.id'
    z' = ℱ.cast[] $ ℱ.inverse-unique₀' 
      (isoⁿ[]→iso[] F'∘F'⁻¹≅Id' (F'.₀' a') 
        ℱ.∘Iso' F'-map-iso F' (isoⁿ[]→iso[] Id'≅F'⁻¹∘'F' a')) 
      ℱ.id-iso↓ zig'

  inverse-equivalence' = record 
    { F'⁻¹ = F' 
    ; F'⊣F'⁻¹ = F'⁻¹⊣F'
    ; unit'-iso = λ x' → ℱ.is-invertible[]-inverse (counit'-iso x') 
    ; counit'-iso = λ x' → ℰ.is-invertible[]-inverse (unit'-iso x') }
```
</details>

As with an ordinary [[equivalence of categories]] there are other ways
of characterising displayed equivalences which will usually be more
convenient when it comes to constructing equivalences by hand.

## Fully faithful, essentially surjective

Here we give the displayed analogue of `ff+split-eso→is-equivalence`{.Agda}, 
requiring a similarly Herculean effort. Suppose $F' : \cE \to_F \cF$ 
is a displayed functor over a [[fully faithful]] and [[split essentially
surjective]] base functor $F : \cA \to \cB$, so that $F'$ is [[fully
faithfully displayed]] and [[essentially split surjective over]] $F$.

```agda
module _
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B} {F' : Displayed-functor F ℰ ℱ}
  (ff : is-fully-faithful F) (eso : is-split-eso F) 
  (ff' : is-ff[] F') (eso' : is-split-eso[ eso ] F')
  where

  private module ff[]+split-eso[]is-equivalence[] where
```

<!--
```agda
    F-is-equiv = ff+split-eso→is-equivalence {F = F} ff eso
    open is-equivalence F-is-equiv

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
    module F = Functor F
    module F' = Displayed-functor F'
    module F⁻¹ = Functor F⁻¹
    module ff {x} {y} = Equiv (F.F₁ , ff {x} {y})
```
-->

Since $F$ is fully faithfully displayed, we can pull back any displayed 
morphism $f'$ over $f$ in $\cF$ to a unique displayed morphism in 
$F'^{-1} f'$ in $\cE$ such  that $F F'^{-1} f'$. However, we must take 
care to transport so that the base of $F'^{-1} f'$ agrees with $F^{-1} f$

```agda
    ff'⁻¹
      : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} 
      → ℱ.Hom[ f ] (F'.₀' x') (F'.₀' y') 
      → ℰ.Hom[ equiv→inverse ff f ] x' y'
    ff'⁻¹ {f = f} f' = equiv→inverse ff' $ ℱ.hom[ sym (ff.ε f) ] f'
```

On account of this transport, we need displayed variants of the usual
`η` and `ε` equalities for the equivalence given by `ff'`{.Agda}.

```agda
    module ff' where
      module _ {x} {y} {f} {x'} {y'} where 
        open Equiv (F'.₁' , ff' {x} {y} {f} {x'} {y'}) public
      ε[]
        : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} 
          (f' : ℱ.Hom[ f ] (F'.₀' x') (F'.₀' y'))
        → F'.₁' (ff'⁻¹ f') ℱ.≡[ ff.ε f ] f'

      η[]
        : ∀ {x y f} {x' : ℰ.Ob[ x ]} {y' : ℰ.Ob[ y ]} (f' : ℰ.Hom[ f ] x' y')
        → ff'⁻¹ (F'.₁' f') ℰ.≡[ ff.η f ] f'
```

<details>
<summary>The derivations of these equalities are a little hairy.</summary>
```agda
      ε[] {f = f} f' = ℱ.begin[]
        F'.₁' (equiv→inverse ff' (ℱ.hom[ sym (ff.ε f) ] f'))  ℱ.≡[]⟨ ε (ℱ.hom[ sym (ff.ε f) ] f') ⟩
        ℱ.hom[ sym (ff.ε f) ] f'                              ℱ.≡[]˘⟨ ℱ.coh[ sym (ff.ε f) ] f' ⟩
        f'                                                    ℱ.∎[]

      η[] {f = f} f' = ℰ.begin[]
        equiv→inverse (ff' {f = ff .is-eqv (F.₁ f) .centre .fst}) (ℱ.hom[ sym (ff.ε (F.₁ f)) ] (F'.₁' f'))  ℰ.≡[]⟨ apd (λ _ → equiv→inverse ff') (ℱ.coh[ ap (F.₁) (ff.η f) ] (ℱ.hom[ sym (ff.ε (F.₁ f)) ] (F'.₁' f'))) ⟩
        equiv→inverse (ff' {f = f}) (ℱ.hom[ ap (F.₁) (ff.η f) ] (ℱ.hom[ sym (ff.ε (F.₁ f)) ] (F'.₁' f')))   ℰ.≡[]⟨ apd (λ _ → equiv→inverse (ff' {f = f})) (ℱ.hom[]-∙ (sym (ff.ε (F.₁ f))) (ap (F.₁) (ff.η f))) ⟩
        equiv→inverse (ff' {f = f}) (ℱ.hom[ sym (ff.ε (F.₁ f)) ∙ ap (F.₁) (ff.η f) ] (F'.₁' f'))            ℰ.≡[]˘⟨ apd (λ _ → equiv→inverse (ff' {f = f})) (ℱ.cast[] $ ℱ.coh[ sym (ff.ε (F.₁ f)) ∙ ap (F.₁) (ff.η f) ]  (F'.₁' f')) ⟩
        equiv→inverse (ff' {f = f}) (F'.₁' f')                                                              ℰ.≡[]⟨ η f' ⟩
        f'                                                                                                  ℰ.∎[]
```
</details>

We can use this together with essential surjectivity to define `F'⁻¹`{.Agda}

```agda
    F'⁻¹ : Displayed-functor F⁻¹ ℱ ℰ
    F'⁻¹ .F₀' b' = eso' b' .fst

    F'⁻¹ .F₁' {x} {y} {f} {x'} {y'} f' = ff'⁻¹ (ffy' ℱ.∘' f' ℱ.∘' ftx') where
      open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
      open Σ (eso' y') renaming (fst to f*y' ; snd to f*y'-iso)
      ftx' = f*x'-iso .ℱ.to'
      ffy' = f*y'-iso .ℱ.from'
    
    F'⁻¹ .F-id' {x} {x'} = ℰ.begin[]
      ff'⁻¹ (ffx' ℱ.∘' ℱ.id' ℱ.∘' ftx') ℰ.≡[]⟨ apd (λ _ f' → ff'⁻¹ (ffx' ℱ.∘' f')) (ℱ.idl' ftx') ⟩
      ff'⁻¹ (ffx' ℱ.∘' ftx')            ℰ.≡[]⟨ apd (λ _ → ff'⁻¹) (f*x'-iso.invr') ⟩
      ff'⁻¹ ℱ.id'                       ℰ.≡[]˘⟨ apd (λ _ → ff'⁻¹) (F' .F-id') ⟩
      ff'⁻¹ (F'.₁' ℰ.id')               ℰ.≡[]⟨ ff'.η[] ℰ.id' ⟩
      ℰ.id'                             ℰ.∎[]
      where
        open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
        module f*x'-iso = ℱ._≅[_]_ f*x'-iso
        ftx' = f*x'-iso.to'
        ffx' = f*x'-iso.from'


    F'⁻¹ .F-∘' {a' = x'} {y'} {z'} {f'} {g'} = ff[]→faithful[] F' ff' $ ℱ.begin[]
      F'.₁' (ff'⁻¹ (ffz' ℱ.∘' (f' ℱ.∘' g') ℱ.∘' ftx'))                                    ℱ.≡[]⟨ ff'.ε[] (ffz' ℱ.∘' (f' ℱ.∘' g') ℱ.∘' ftx') ⟩
      ffz' ℱ.∘' (f' ℱ.∘' g') ℱ.∘' ftx'                                                    ℱ.≡[]˘⟨ apd (λ _ → ffz' ℱ.∘'_) (ℱ.assoc' f' g' ftx') ⟩
      ffz' ℱ.∘' f' ℱ.∘' g' ℱ.∘' ftx'                                                      ℱ.≡[]˘⟨ apd (λ _ h' → ffz' ℱ.∘' f' ℱ.∘' h') (ℱ.idl' (g' ℱ.∘' ftx')) ⟩
      ffz' ℱ.∘' f' ℱ.∘' ℱ.id' ℱ.∘' g' ℱ.∘' ftx'                                           ℱ.≡[]˘⟨ apd (λ _ h' → ffz' ℱ.∘' f' ℱ.∘' h' ℱ.∘' g' ℱ.∘' ftx')  (f*y'-iso .ℱ.invl') ⟩
      ffz' ℱ.∘' f' ℱ.∘' (fty' ℱ.∘' ffy') ℱ.∘' g' ℱ.∘' ftx'                                ℱ.≡[]˘⟨ apd (λ _ h' → ffz' ℱ.∘' f' ℱ.∘' h') (ℱ.assoc' fty' ffy' (g' ℱ.∘' ftx')) ⟩
      ffz' ℱ.∘' f' ℱ.∘' fty' ℱ.∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')                                ℱ.≡[]⟨ apd (λ _ → ffz' ℱ.∘'_) (ℱ.assoc' f' fty' (ffy' ℱ.∘' g' ℱ.∘' ftx'))⟩
      ffz' ℱ.∘' (f' ℱ.∘' fty') ℱ.∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')                              ℱ.≡[]⟨ ℱ.assoc' ffz' (f' ℱ.∘' fty') (ffy' ℱ.∘' g' ℱ.∘' ftx') ⟩
      (ffz' ℱ.∘' f' ℱ.∘' fty') ℱ.∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')                              ℱ.≡[]˘⟨ apd (λ _ → ℱ._∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')) (ff'.ε[] (ffz' ℱ.∘' f' ℱ.∘' fty')) ⟩
      F'.₁' (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty')) ℱ.∘' (ffy' ℱ.∘' g' ℱ.∘' ftx')                ℱ.≡[]˘⟨ apd (λ _ → F'.₁' (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty')) ℱ.∘'_) (ff'.ε[] (ffy' ℱ.∘' g' ℱ.∘' ftx')) ⟩
      F'.₁' (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty')) ℱ.∘' F'.₁' (ff'⁻¹ (ffy' ℱ.∘' g' ℱ.∘' ftx'))  ℱ.≡[]˘⟨ F' .F-∘' {f' = (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty'))} {g' = (ff'⁻¹ (ffy' ℱ.∘' g' ℱ.∘' ftx'))}⟩
      F'.₁' (ff'⁻¹ (ffz' ℱ.∘' f' ℱ.∘' fty') ℰ.∘' ff'⁻¹ (ffy' ℱ.∘' g' ℱ.∘' ftx'))          ℱ.∎[]
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

<details>
<summary>Defining the displayed unit, counit, and associated identities
are all given by straightforward (if tedious) adaptions of those for
`ff+split-eso→is-equivalence`{.Agda}, and are given without commentary.
</summary>
```agda
    module F'⁻¹ = Displayed-functor F'⁻¹

    module F'⊣F'⁻¹ where
      open _=[_]=>_

      unit' : Id' =[ unit ]=> F'⁻¹ F∘' F'
      unit' .η' x' = ff'⁻¹ ffx' where
        open Σ (eso' (F'.₀' x')) renaming (fst to f*x' ; snd to f*x'-iso)
        ffx' = f*x'-iso .ℱ.from'

      unit' .is-natural' x' y' f' = ff[]→faithful[] F' ff' $ ℱ.begin[]
        F'.₁' (η'y' ℰ.∘' f')                                                  ℱ.≡[]⟨ F'.F-∘' ⟩
        F'.₁' (ff'⁻¹ ffy') ℱ.∘' F'.₁' f'                                      ℱ.≡[]⟨ ff'.ε[] ffy' ℱ.⟩∘'⟨refl ⟩
        ffy' ℱ.∘' F'.₁' f'                                                    ℱ.≡[]˘⟨ ℱ.refl⟩∘'⟨ ℱ.idr' _ ⟩
        ffy' ℱ.∘' F'.₁' f' ℱ.∘' ℱ.id'                                         ℱ.≡[]˘⟨ ℱ.refl⟩∘'⟨ ℱ.refl⟩∘'⟨ f*x'-iso.invl' ⟩
        ffy' ℱ.∘' F'.₁' f' ℱ.∘' ftx' ℱ.∘' ffx'                                ℱ.≡[]⟨ (ℱ.refl⟩∘'⟨ ℱ.assoc' _ _ _ ) ℱ.∙[]  ℱ.assoc' _ _ _ ⟩
        (ffy' ℱ.∘' F'.₁' f' ℱ.∘' ftx') ℱ.∘' ffx'                              ℱ.≡[]˘⟨ ff'.ε[] _ ℱ.⟩∘'⟨ ff'.ε[] _ ⟩
        F'.₁' (ff'⁻¹ (ffy' ℱ.∘' F'.₁' f' ℱ.∘' ftx')) ℱ.∘' F'.₁' (ff'⁻¹ ffx')  ℱ.≡[]˘⟨ F'.F-∘' ⟩
        F'.₁' (₁' (F'⁻¹ F∘' F') f' ℰ.∘' η'x')                                 ℱ.∎[]
        where
          open Σ (eso' (F'.₀' x')) renaming (fst to f*x' ; snd to f*x'-iso)
          open Σ (eso' (F'.₀' y')) renaming (fst to f*y' ; snd to f*y'-iso)
          module f*x'-iso = ℱ._≅[_]_ f*x'-iso
          module f*y'-iso = ℱ._≅[_]_ f*y'-iso
          ffx' = f*x'-iso.from'
          ffy' = f*y'-iso.from'
          ftx' = f*x'-iso.to'
          η'x' = unit' .η' x'
          η'y' = unit' .η' y'
    
      counit' : F' F∘' F'⁻¹ =[ counit ]=> Id'
      counit' .η' x' = ftx' where
        open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
        ftx' = f*x'-iso .ℱ.to'
    
      counit' .is-natural' x' y' f' = ℱ.begin[]
        fty' ℱ.∘' F'.₁' (ff'⁻¹ (ffy' ℱ.∘' f' ℱ.∘' ftx'))  ℱ.≡[]⟨ ℱ.refl⟩∘'⟨ ff'.ε[] _ ⟩
        fty' ℱ.∘' ffy' ℱ.∘' f' ℱ.∘' ftx'                  ℱ.≡[]⟨ ℱ.cancell[] _ f*y'-iso.invl' ⟩
        f' ℱ.∘' ftx'                                      ℱ.∎[]
        where
          open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
          open Σ (eso' y') renaming (fst to f*y' ; snd to f*y'-iso)
          module f*x'-iso = ℱ._≅[_]_ f*x'-iso
          module f*y'-iso = ℱ._≅[_]_ f*y'-iso
          ffy' = f*y'-iso.from'
          ftx' = f*x'-iso.to'
          fty' = f*y'-iso.to'
    
      zig' 
        : ∀ {x} {x' : ℰ.Ob[ x ]} 
        → counit' .η' (F'.₀' x') ℱ.∘' F'.₁' (unit' .η' x') ℱ.≡[ zig ] ℱ.id'
      zig' {x' = x'} = ℱ.begin[]
        ftx' ℱ.∘' F'.₁' (ff'⁻¹ ffx')  ℱ.≡[]⟨ ℱ.refl⟩∘'⟨ ff'.ε[] _ ⟩
        ftx' ℱ.∘' ffx'                ℱ.≡[]⟨ f*x'-iso.invl' ⟩
        ℱ.id'                         ℱ.∎[]
        where
          open Σ (eso' (F'.₀' x')) renaming (fst to f*x' ; snd to f*x'-iso)
          module f*x'-iso = ℱ._≅[_]_ f*x'-iso
          ftx' = f*x'-iso.to'
          ffx' = f*x'-iso.from'

      zag'
        : ∀ {x} {x' : ℱ.Ob[ x ]}
        → F'⁻¹.₁' (counit' .η' x') ℰ.∘' unit' .η' (F'⁻¹.₀' x') ℰ.≡[ zag ] ℰ.id'
      zag' {x' = x'} = ff[]→faithful[] F' ff' $ ℱ.begin[]
        F'.₁' (ff'⁻¹ (ffx' ℱ.∘' ftx' ℱ.∘' fftx') ℰ.∘' ff'⁻¹ fffx')            ℱ.≡[]⟨ F'.F-∘' ⟩
        F'.F₁' (ff'⁻¹ (ffx' ℱ.∘' ftx' ℱ.∘' fftx')) ℱ.∘' F'.F₁' (ff'⁻¹ fffx')  ℱ.≡[]⟨ ff'.ε[] _ ℱ.⟩∘'⟨ ff'.ε[] _ ⟩
        (ffx' ℱ.∘' ftx' ℱ.∘' fftx') ℱ.∘' fffx'                                ℱ.≡[]⟨ (ℱ.assoc' _ _ _ ℱ.⟩∘'⟨refl) ⟩
        ((ffx' ℱ.∘' ftx') ℱ.∘' fftx') ℱ.∘' fffx'                              ℱ.≡[]˘⟨ ℱ.assoc' _ _ _ ⟩
        (ffx' ℱ.∘' ftx') ℱ.∘' (fftx' ℱ.∘' fffx')                              ℱ.≡[]⟨ f*x'-iso.invr' ℱ.⟩∘'⟨ f*f*x'-iso.invl' ⟩
        ℱ.id' ℱ.∘' ℱ.id'                                                      ℱ.≡[]⟨ ℱ.idl' _ ⟩
        ℱ.id'                                                                 ℱ.≡[]˘⟨ F'.F-id' ⟩
        F'.₁' ℰ.id'                                                           ℱ.∎[]
        where
          open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
          open Σ (eso' (F'.₀' f*x')) renaming (fst to f*f*x' ; snd to f*f*x'-iso)
          module f*x'-iso = ℱ._≅[_]_ f*x'-iso
          module f*f*x'-iso = ℱ._≅[_]_ f*f*x'-iso
          ftx' = f*x'-iso.to'
          ffx' = f*x'-iso.from'
          fftx' = f*f*x'-iso.to'
          fffx' = f*f*x'-iso.from'

    open F'⊣F'⁻¹
  
    F'⊣F'⁻¹ : F' ⊣[ F⊣F⁻¹ ] F'⁻¹
    F'⊣F'⁻¹ = record { F'⊣F'⁻¹ }

    unit'-iso : ∀ {x} x' → ℰ.is-invertible[ unit-iso x ] (unit' .η' x')
    unit'-iso x' = record 
      { inv' = ff'⁻¹ ftx' 
      ; inverses' = record 
        { invl' = ff[]→faithful[] F' ff' $ ℱ.begin[]
          F'.₁' (ff'⁻¹ ffx' ℰ.∘' ff'⁻¹ ftx')          ℱ.≡[]⟨ F'.F-∘' ⟩
          F'.₁' (ff'⁻¹ ffx') ℱ.∘' F'.₁' (ff'⁻¹ ftx')  ℱ.≡[]⟨ ff'.ε[] _ ℱ.⟩∘'⟨ ff'.ε[] _ ⟩
          ffx' ℱ.∘' ftx'                              ℱ.≡[]⟨ f*x'-iso.invr' ⟩
          ℱ.id'                                       ℱ.≡[]˘⟨ F'.F-id' ⟩
          F'.₁' ℰ.id'                                 ℱ.∎[]
        ; invr' = ff[]→faithful[] F' ff' $ ℱ.begin[]
          F'.₁' (ff'⁻¹ ftx' ℰ.∘' ff'⁻¹ ffx')          ℱ.≡[]⟨ F'.F-∘' ⟩
          F'.₁' (ff'⁻¹ ftx') ℱ.∘' F'.₁' (ff'⁻¹ ffx')  ℱ.≡[]⟨ ff'.ε[] _ ℱ.⟩∘'⟨ ff'.ε[] _ ⟩
          ftx' ℱ.∘' ffx'                              ℱ.≡[]⟨ f*x'-iso.invl' ⟩
          ℱ.id'                                       ℱ.≡[]˘⟨ F'.F-id' ⟩
          F'.₁' ℰ.id' ℱ.∎[]
        } 
      }
      where 
        open Σ (eso' (F'.₀' x')) renaming (fst to f*x' ; snd to f*x'-iso)
        module f*x'-iso = ℱ._≅[_]_ f*x'-iso
        ftx' = f*x'-iso.to'
        ffx' = f*x'-iso.from'

    counit'-iso : ∀ {x} x' → ℱ.is-invertible[ counit-iso x ] (counit' .η' x')
    counit'-iso x' = record { f*x'-iso } where
      open Σ (eso' x') renaming (fst to f*x' ; snd to f*x'-iso)
      module f*x'-iso = ℱ._≅[_]_ f*x'-iso
  
  open ff[]+split-eso[]is-equivalence[]
```
</details>

<!-- 
```agda
  ff[_]+split-eso[_]→inverse] = F'⁻¹
  ff[_]+split-eso[_]→unit' = F'⊣F'⁻¹.unit'
  ff[_]+split-eso[_]→counit' = F'⊣F'⁻¹.counit'
  ff[_]+split-eso[_]→F'⊣inverse' = F'⊣F'⁻¹
  ff[_]+split-eso[_]→unit'-iso = unit'-iso
  ff[_]+split-eso[_]→counit'-iso = counit'-iso
```
-->

```agda
  ff[_]+split-eso[_]→is-equivalence[] : is-equivalence[ F-is-equiv ] F'
  ff[_]+split-eso[_]→is-equivalence[] = record { ff[]+split-eso[]is-equivalence[] }
```
