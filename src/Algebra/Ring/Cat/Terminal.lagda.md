<!--
```agda
open import Algebra.Ring.Instances.Lift
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Diagram.Terminal
open import Cat.Prelude hiding (_+_ ; _*_)

import Algebra.Ring.Reasoning as Kit

open is-ring-hom
```
-->

```agda
module Algebra.Ring.Cat.Terminal where
```

# The terminal ring {defines="terminal-ring"}

<!--
```agda
variable
  ℓ : Level
  A : Type ℓ
  Aᴿ : Ring-on A
```
-->

In the introduction it was mentioned that the [[zero ring]] — which is
not a zero object — is a terminal object. Since the underlying set
$\top$ is already terminal in $\Set$, we only need to show that any
function $A \to 0$ is a ring morphism.

```agda
!ring-hom : is-ring-hom Aᴿ (Zero-ring .snd) λ _ → tt
!ring-hom .pres-id    = refl
!ring-hom .pres-+ _ _ = refl
!ring-hom .pres-* _ _ = refl
```

Then we just need to lift this into the category we are interested in.

```agda
module _ {ℓ : Level} where
  Lift0 : Ring ℓ
  Lift0 = Lift-ring ℓ Zero-ring

  Lift0-is-terminal : is-terminal (Rings ℓ) Lift0
  Lift0-is-terminal R = contr (∫hom _ (Lift-ring-hom-r !ring-hom)) λ _ → ext λ _ → prop!
```
