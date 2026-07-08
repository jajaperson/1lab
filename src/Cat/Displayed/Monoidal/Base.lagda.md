<!--
```agda
open import Cat.Displayed.Functor.Bifunctor.Assoc
open import Cat.Displayed.Instances.TotalProduct
open import Cat.Displayed.Functor.Naturality
open import Cat.Displayed.Functor.Bifunctor
open import Cat.Displayed.Instances.Functor
open import Cat.Displayed.Functor
open import Cat.Functor.Bifunctor
open import Cat.Displayed.Base
open import Cat.Monoidal.Base
open import Cat.Prelude

import Cat.Displayed.Morphism.Reasoning as Dr
import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Monoidal.Base where
```
<!--
```agda
private
  variable
    o ℓ o' ℓ' o'' ℓ'' o''' ℓ''' :  Level
```
-->

# Displayed monoidal categories {defines="displayed-monoidal-category"}

Just as [[displayed categories]] allow us to build categorical structure
atop the structure of a base category, **displayed monoidal categories**
allow us to build monoidal structure atop the structure of a base
[[monoidal category]].

Suppose $\cC$ is a monoidal category and $\cM \liesover \cC$ is
displayed thereover.

```agda
record Displayed-monoidal[_]
  {C : Precategory o ℓ} (Cᵐ : Monoidal-category C) (ℳ : Displayed C o' ℓ')
  : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  no-eta-equality
  open Monoidal-category Cᵐ public
```

<!--
```agda
  open Cr C
  open Dr ℳ
```
-->

To define a monoidal structure on $\cM$, we begin by defining a tensor
product, which is a [[displayed bifunctor]] over the tensor product on
$\cC$, and a tensor unit, which is an object displayed over the tensor
unit of $\cC$.

```agda
  field
    -⊗'-  : Displayed-bifunctor -⊗- ℳ ℳ ℳ
    Unit' : Ob[ Unit ]
```

<!--
```agda
  private
    [ℳ,ℳ] = DisCat[ ℳ , ℳ ]
    module [ℳ,ℳ] = Dr [ℳ,ℳ]

    [ℳ³,ℳ] = DisCat[ ℳ ×ᵀᴰ ℳ ×ᵀᴰ ℳ , ℳ ]
    module [ℳ³,ℳ] = Dr [ℳ³,ℳ]

    ⊗'-assocˡ' = assocˡ' {O = ⊤} {λ _ _ → C} {λ _ → ⊤} (λ _ _ → ℳ) -⊗'-
    ⊗'-assocʳ' = assocʳ' {O = ⊤} {λ _ _ → C} {λ _ → ⊤} (λ _ _ → ℳ) -⊗'-

  module -⊗'- = Displayed-bifunctor -⊗'- hiding (_◀'_ ; _▶'_ ; F₀')
  open Displayed-bifunctor -⊗'- public using (_◀'_ ; _▶'_) renaming (F₀' to infixr 25 _⊗'_ ; _◆'_ to infix 25 _⊗₁'_)
  open Displayed-functor
```
-->

The unit and associativity laws are witnessed by [[displayed natural
isomorphisms]] over the corresponding witnesses for $\cC$.

```agda
  field
    unitor-l' : Id' [ℳ,ℳ].≅[ unitor-l ] (-⊗'-.Right' Unit')
    unitor-r' : Id' [ℳ,ℳ].≅[ unitor-r ] (-⊗'-.Left' Unit')
    associator' : ⊗'-assocˡ' [ℳ³,ℳ].≅[ associator ] ⊗'-assocʳ'
```

<!--
```agda
  module unitor-l' = [ℳ,ℳ]._≅[_]_ unitor-l'
  module unitor-r' = [ℳ,ℳ]._≅[_]_ unitor-r'
  module associator' = [ℳ³,ℳ]._≅[_]_ associator'

  private
    open module λ←' = _=[_]=>_ unitor-l'.from' public using () renaming (η' to λ←')
    open module λ→' = _=[_]=>_ unitor-l'.to'   public using () renaming (η' to λ→')

    open module ρ←' = _=[_]=>_ unitor-r'.from' public using () renaming (η' to ρ←')
    open module ρ→' = _=[_]=>_ unitor-r'.to'   public using () renaming (η' to ρ→')

    open module α←' = _=[_]=>_ associator'.from' public using () renaming (η' to α←')
    open module α→' = _=[_]=>_ associator'.to'   public using () renaming (η' to α→')

  λ≅' : ∀ {x x'} → x' ≅[ λ≅ {x} ] Unit' ⊗' x'
  λ≅' = isoⁿ[]→iso[] unitor-l' _

  ρ≅' : ∀ {x x'} → x' ≅[ ρ≅ {x} ] x' ⊗' Unit'
  ρ≅' = isoⁿ[]→iso[] unitor-r' _
```
-->

Finally, we need displayed analogues of the `triangle`{.Agda} and
`pentagon`{.Agda} coherence laws.

```agda
  field
    triangle'
      : ∀ {x z x' z'}
      → (ρ←' x' ◀' z') ∘' α←' (x' , Unit' , z') ≡[ triangle {x} {z} ] x' ▶' λ←' z'

    pentagon'
      : ∀ {x y z w x' y' z' w'}
      → (α←' (x' , y' , z') ◀' w') ∘' α←' (x' , y' ⊗' z' , w') ∘' (x' ▶' α←' (y' , z' , w'))
        ≡[ pentagon {x} {y} {z} {w} ]
        α←' (x' ⊗' y' , z' , w') ∘' α←' (x' , y' , z' ⊗' w')
```
