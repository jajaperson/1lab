<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Displayed.Functor.Bifunctor.Total
open import Cat.Displayed.Functor.Total
open import Cat.Displayed.Instances.TotalProduct
open import Cat.Displayed.Functor.Bifunctor
open import Cat.Displayed.Instances.Functor
open import Cat.Displayed.Functor
open import Cat.Functor.Bifunctor
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Functor.Bifunctor.Assoc as Assoc
import Cat.Displayed.Morphism as Dm

--remove me
open import Cat.Displayed.Total
open import Cat.Instances.Product

open Displayed-functor
open Displayed
```
-->

```agda
module Cat.Displayed.Functor.Bifunctor.Assoc
  {o o' ℓ ℓ' d d'}
  {O : Type o}
  {H : O → O → Precategory ℓ ℓ'}
  {O[_] : O → Type o'}
  {F : ∀ {A B C} → Bifunctor (H B C) (H A B) (H A C)}
  (H' : ∀ {A B} → O[ A ] → O[ B ] → Displayed (H A B) d d')
  (F'
    : ∀ {A B C} {A' : O[ A ]} {B' : O[ B ]} {C' : O[ C ]}
    → Displayed-bifunctor F (H' B' C') (H' A' B') (H' A' C')
  )
  where
```

<!--
```agda
private
  module F where
    module _ {A B C} where open Bifunctor (F {A} {B} {C}) public
    open Assoc H F public
  module F' {A B C} {A' : O[ A ]} {B' : O[ B ]} {C' : O[ C ]} =
    Displayed-bifunctor (F' {A' = A'} {B'} {C'})
  module H' {A B} {A' : O[ A ]} {B' : O[ B ]} = Displayed (H' A' B')

```
-->

# Associations of nested displayed bifunctors

In this module we define analogues of `assocˡ`{.Agda} and `assocʳ'`{.Agda}
at the generality of a family `F'`{.Agda} of [[displayed bifunctors]]
defined on a family `H'`{.Agda} of displayed categories.

```agda
module _
  {A B C D} {A' : O[ A ]} {B' : O[ B ]} {C' : O[ C ]} {D' : O[ D ]}
  where
```

<!--
```agda
  private
    module C'D' = Displayed (H' C' D')
    module B'C' = Displayed (H' B' C')
    module A'B' = Displayed (H' A' B')
    module A'D' = Displayed (H' A' D')
    module B'D' = Displayed (H' B' D')
    module A'C' = Displayed (H' A' C')
```
-->

```agda
  assocˡ' : Displayed-functor F.assocˡ (H' C' D' ×ᵀᴰ H' B' C' ×ᵀᴰ H' A' B') (H' A' D')
  assocˡ' .F₀' (x' , y' , z') = F' · (F' · x' · y') · z'
  assocˡ' .F₁' (f' , g' , h') = (f' F'.◆' g') F'.◆' h'
  assocˡ' .F-id' {x} {x'} = H'.begin[]
    (C'D'.id' F'.◆' B'C'.id') F'.◆' A'B'.id'  H'.≡[]⟨ apd (λ _ → F'._◆' A'B'.id' {x .snd .snd} {x' .snd .snd}) F'.◆-id' ⟩
    B'D'.id' F'.◆' A'B'.id'                   H'.≡[]⟨ F'.◆-id' ⟩
    A'D'.id'                                  H'.∎[]
  assocˡ' .F-∘' {f' = (f₁' , f₂' , f₃')} {(g₁' , g₂' , g₃')} = H'.begin[]
    ((f₁' C'D'.∘' g₁') F'.◆' (f₂' B'C'.∘' g₂')) F'.◆' (f₃' A'B'.∘' g₃') H'.≡[]⟨ apd (λ _ → F'._◆' (f₃' A'B'.∘' g₃')) F'.◆-∘' ⟩
    ((f₁' F'.◆' f₂') B'D'.∘' (g₁' F'.◆' g₂')) F'.◆' (f₃' A'B'.∘' g₃')   H'.≡[]⟨ F'.◆-∘' ⟩
    ((f₁' F'.◆' f₂') F'.◆' f₃') A'D'.∘' ((g₁' F'.◆' g₂') F'.◆' g₃')     H'.∎[]

  assocʳ' : Displayed-functor F.assocʳ (H' C' D' ×ᵀᴰ H' B' C' ×ᵀᴰ H' A' B') (H' A' D')
  assocʳ' .F₀' (x' , y' , z') = F' · x' · (F' · y' · z')
  assocʳ' .F₁' (f' , g' , h') = f' F'.◆' (g' F'.◆' h')
  assocʳ' .F-id' {x} {x'} = H'.begin[]
    C'D'.id' F'.◆' (B'C'.id' F'.◆' A'B'.id')  H'.≡[]⟨ apd (λ _ → C'D'.id' {x .fst} {x' .fst} F'.◆'_) F'.◆-id' ⟩
    C'D'.id' F'.◆' A'C'.id'                   H'.≡[]⟨ F'.◆-id' ⟩
    A'D'.id'                                  H'.∎[]
  assocʳ' .F-∘' {f' = (f₁' , f₂' , f₃')} {(g₁' , g₂' , g₃')} = H'.begin[]
    (f₁' C'D'.∘' g₁') F'.◆' ((f₂' B'C'.∘' g₂') F'.◆' (f₃' A'B'.∘' g₃')) H'.≡[]⟨ apd (λ _ → (f₁' C'D'.∘' g₁') F'.◆'_) F'.◆-∘' ⟩
    (f₁' C'D'.∘' g₁') F'.◆' ((f₂' F'.◆' f₃') A'C'.∘' (g₂' F'.◆' g₃'))   H'.≡[]⟨ F'.◆-∘' ⟩
    (f₁' F'.◆' (f₂' F'.◆' f₃')) A'D'.∘' (g₁' F'.◆' (g₂' F'.◆' g₃'))     H'.∎[]
```

The [[total functor]] of `assocˡ'`{.Agda} is isomorphic to `assocˡ‵{.Agda}
of the [[total bifunctor]].

```agda
  -- ∫ᶠassocˡ'≅assocˡ : ∫ᶠ assocˡ' ≅ⁿ {! F.assocˡ !}
```

A witness of associativity of the displayed bifunctor is a natural
transformation displayed over the `Associator-for`{.Agda} the underlying
bifunctor.

```agda
Associator-for[_] : F.Associator-for → Type _
Associator-for[ α ] = ∀ {A B C D}
  → {A' : O[ A ]} {B' : O[ B ]} {C' : O[ C ]} {D' : O[ D ]}
  → let open Dm DisCat[ H' C' D' ×ᵀᴰ H' B' C' ×ᵀᴰ H' A' B' , H' A' D' ]
    in assocˡ' ≅[ α ] assocʳ'
```
