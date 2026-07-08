<!--
```agda
open import Cat.Displayed.Instances.Functor
open import Cat.Displayed.Functor
open import Cat.Functor.Bifunctor
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as Dr
import Cat.Functor.Reasoning as Fr

open _=[_]=>_
```
-->

```agda
module Cat.Displayed.Functor.Bifunctor where
```

# Displayed bifunctors {defines="displayed-bifunctor"}

<!--
```agda
private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ : Level
    C D E : Precategory o ℓ
    C' D' E' : Displayed C o ℓ
    F : Bifunctor C D E
```
-->

In the 1Lab, we define a [[bifunctor]] $F$ from $\cC$ and $\cD$ to $\cE$
in curried form, as a functor $F : \cC \to [\cD, \cE]$, for technical
reasons. Given displayed categories $\cC' \liesover \cC$, $\cD'
\liesover \cD$, and $\cE' \liesover \cE$, we define a **displayed
bifunctor** $F'$ from $\cC'$ and $\cD'$ to $\cE'$ _over_ $F$ in the same
way, as a [[displayed functor]] over $F$ into the [[displayed functor
category]] $[\cC' , \cD']$.

```agda
Displayed-bifunctor
  : (F : Bifunctor C D E)
  → Displayed C o ℓ → Displayed D o₁ ℓ₁ → Displayed E o₂ ℓ₂ → Type _
Displayed-bifunctor F C' D' E' = Displayed-functor F C' DisCat[ D' , E' ]
```

<!--
```agda
level-of-bifunctor : (F : Bifunctor C D E) → Displayed C o ℓ → Displayed D o₁ ℓ₁ → Displayed E o₂ ℓ₂ → Level
level-of-bifunctor F C' D' E' = level-of (Displayed-bifunctor F C' D' E')

{-# DISPLAY Displayed-functor F C' (DisCat[_,_] D' E') = Bifunctor F C' D' E' #-}

module Displayed-bifunctor {C' : Displayed C o ℓ} {D' : Displayed D o₁ ℓ₁} {E' : Displayed E o₂ ℓ₂} (F' : Displayed-bifunctor F C' D' E') where
  private
    module C = Precategory C
    module D = Precategory D
    module E = Precategory E
    module C' = Dr C'
    module D' = Dr D'
    module E' = Dr E'
    open module F = Bifunctor F
    module F' = Displayed-functor F'

    variable
      a b c : C.Ob
      x y z : D.Ob
      α β γ : C.Hom a b
      f g h : D.Hom x y
      a' b' c' : C'.Ob[ a ]
      x' y' z' : D'.Ob[ x ]

  private
    open module r₀ {x} x' = Displayed-functor (F'.F₀' {x = x} x') public
      renaming (F₁' to infix 35 _▶'_) using (F₀')

    open module r₁ {a b} {f : C.Hom a b} {a' b'} (f' : C'.Hom[ f ] a' b') = _=[_]=>_ (F'.F₁' f') public
      renaming (η' to infix 35 _◀'_) using ()
```
-->

As in the case of ordinary bifunctors, we define helpers for working
with the two functorial actions:

```agda
  lmap' : C'.Hom[ α ] a' b' → E'.Hom[ lmap α ] (F₀' a' x') (F₀' b' x')
  lmap' f = f ◀' _

  rmap' : D'.Hom[ f ] x' y' → E'.Hom[ rmap f ] (F₀' a' x') (F₀' a' y')
  rmap' f = _ ▶' f

  lmap-id'
    : ∀ {x a x' a'} → lmap' C'.id' E'.≡[ lmap-id {x} {a} ] E'.id' {x = F₀' x' a'}
  lmap-id' =  F'.F-id' ηₚ' _

  lmap-∘'
    : {α' : C'.Hom[ α ] b' c'} {β' : C'.Hom[ β ] a' b'}
    → lmap' {x' = x'} (α' C'.∘' β') E'.≡[ lmap-∘ α β ] (lmap' α' E'.∘' lmap' β')
  lmap-∘' = F'.F-∘' ηₚ' _

  rmap-id'
    : ∀ {a x a' x'} → rmap' D'.id' E'.≡[ rmap-id {a} {x} ] E'.id' {x = F₀' a' x'}
  rmap-id' = F'.F₀' _ .Displayed-functor.F-id'

  rmap-∘'
    : {f' : D'.Hom[ f ] y' z'} {g' : D'.Hom[ g ] x' y'}
    → rmap' {a' = a'} (f' D'.∘' g') E'.≡[ rmap-∘ f g ] (rmap' f' E'.∘' rmap' g')
  rmap-∘' = F'.F₀' _ .Displayed-functor.F-∘'

  lrmap'
    : ∀ (α' : C'.Hom[ α ] a' b') (f' : D'.Hom[ f ] x' y')
    → (α' ◀' y') E'.∘' (a' ▶' f') E'.≡[ lrmap _ _ ] (b' ▶' f') E'.∘' (α' ◀' x')
  lrmap' α' f' = F'.F₁' α' .is-natural' _ _ f'
```

## Horizontal composition

We define the **horizontal composition** operation as follows

```agda
  _◆'_ : C'.Hom[ α ] a' b' → D'.Hom[ f ] x' y' → E'.Hom[ α ◆ f ]  (F₀' a' x') (F₀' b' y')
  _◆'_ α' f' = (α' ◀' _) E'.∘' (_ ▶' f')
```

Displayed bifunctors are also functorial in both variables.

```agda
  ◆-id' : (C'.id' {a} {a'} ◆' D'.id' {x} {x'}) E'.≡[ ◆-id ] E'.id'
  ◆-id' = E'.begin[]
    (C'.id' ◀' _) E'.∘' (_ ▶' D'.id') E'.≡[]⟨ E'.eliml[] lmap-id lmap-id' ⟩
    _ ▶' D'.id'                       E'.≡[]⟨ rmap-id' ⟩
    E'.id'                            E'.∎[]

  ◆-∘'
    : ∀ {α' : C'.Hom[ α ] b' c'} {β' : C'.Hom[ β ] a' b'}
      {f' : D'.Hom[ f ] y' z'} {g' : D'.Hom[ g ] x' y'}
    → ((α' C'.∘' β') ◆' (f' D'.∘' g')) E'.≡[ ◆-∘ ] (α' ◆' f') E'.∘' (β' ◆' g')
  ◆-∘' {α' = α'} {β'} {f'} {g'}  = E'.begin[]
    (α' C'.∘' β' ◀' _) E'.∘' (_ ▶' f' D'.∘' g')                   E'.≡[]⟨ lmap-∘' E'.⟩∘'⟨ rmap-∘' ⟩
    ((α' ◀' _) E'.∘' (β' ◀' _)) E'.∘' ((_ ▶' f') E'.∘' (_ ▶' g')) E'.≡[]⟨ E'.extendr[] _ (E'.extendl[] _ (lrmap' _ _)) ⟩
    ((α' ◀' _) E'.∘' (_ ▶' f')) E'.∘' ((β' ◀' _) E'.∘' (_ ▶' g')) E'.∎[]
```

## Associated functors

We can also define displayed analogues of `Right`{.Agda} and `Left`{.Agda}.

```agda
  Right' : C'.Ob[ a ] → Displayed-functor (Right a) D' E'
  Right' a' = F'.F₀' a'

  Left' : D'.Ob[ x ] → Displayed-functor (Left x) C' E'
  Left' x' = record where
    F₀' a' =  F₀' a' x'
    F₁' α' =  α' ◀' x'
    F-id'  =  lmap-id'
    F-∘'   =  lmap-∘'
```

<!--
```agda
  module ▶' {a a'} = Displayed-functor (Right' {a} a') hiding (F₀' ; F₁')
  module ◀' {x x'} = Displayed-functor (Left' {x} x')  hiding (F₀' ; F₁')

module _ {C' : Displayed C o ℓ} {D' : Displayed D o₁ ℓ₁} {E' : Displayed E o₂ ℓ₂} (F : Bifunctor C D E) where
  private
    module C = Precategory C
    module D = Precategory D
    module E = Precategory E
    module C' = Displayed C'
    module D' = Displayed D'
    module E' = Displayed E'
    open module F = Bifunctor F

    variable
      a b c : C.Ob
      x y z : D.Ob
      α β γ : C.Hom a b
      f g h : D.Hom x y
      a' b' c' : C'.Ob[ a ]
      x' y' z' : D'.Ob[ x ]

  record Make-displayed-bifunctor : Type (level-of-bifunctor F C' D' E') where
    field
      F₀' : ∀ {x y} (x' : C'.Ob[ x ]) (y' : D'.Ob[ y ]) → E'.Ob[ F₀ x y  ]

      lmap' : C'.Hom[ α ] a' b' → E'.Hom[ lmap α ] (F₀' a' x') (F₀' b' x')
      lmap-id'
        : ∀ {x a x' a'} → (lmap' C'.id') E'.≡[ lmap-id {x} {a} ] E'.id' {x = F₀' x' a'}
      lmap-∘'
        : {α' : C'.Hom[ α ] b' c'} {β' : C'.Hom[ β ] a' b'}
        → lmap' {x' = x'} (α' C'.∘' β') E'.≡[ lmap-∘ α β ] (lmap' α' E'.∘' lmap' β')

      rmap' : D'.Hom[ f ] x' y' → E'.Hom[ rmap f ] (F₀' a' x') (F₀' a' y')
      rmap'-id
        : ∀ {x a x' a'} → rmap' D'.id' E'.≡[ rmap-id {x} {a} ] E'.id' {x = F₀' x' a'}
      rmap-∘'
        : {f' : D'.Hom[ f ] y' z'} {g' : D'.Hom[ g ] x' y'}
        →  rmap' {a' = a'} (f' D'.∘' g') E'.≡[ rmap-∘ f g ] (rmap' f' E'.∘' rmap' g')

      lrmap' : (α' : C'.Hom[ α ] a' b') (f' : D'.Hom[ f ] x' y')
        → lmap' α' E'.∘' rmap' f' E'.≡[ lrmap α f ] rmap' f' E'.∘' lmap' α'

  make-displayed-bifunctor : Make-displayed-bifunctor → Displayed-bifunctor F C' D' E'
  {-# INLINE make-displayed-bifunctor #-}
  make-displayed-bifunctor m = record
    { F₀' = λ x' → record
      { F₀' = F₀' x'
      ; F₁' =  rmap'
      ; F-id' = rmap'-id
      ; F-∘' =  rmap-∘'
      }
    ; F₁' = λ x' →  record
      { η' = λ y' →  lmap' x'
      ; is-natural' = λ _ _ _ → lrmap' _ _
      }
    ; F-id' =  Nat'-path λ _  → lmap-id'
    ; F-∘'  = Nat'-path λ _ → lmap-∘'
    }
    where open Make-displayed-bifunctor m
```
-->
