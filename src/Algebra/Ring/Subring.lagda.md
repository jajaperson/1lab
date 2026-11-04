<!--
```agda
open import 1Lab.Prelude

open import Algebra.Ring

open import Data.Power

import Cat.Displayed.Instances.Subobjects
```
-->

```agda
module Algebra.Ring.Subring where
```

<!--
```agda
private variable
  ℓ : Level
  R S : Ring ℓ 
private module _ {ℓ} where open Cat.Displayed.Instances.Subobjects (Rings ℓ) hiding (to ; from) public
```
-->

# Subrings

A **subring** $m$ of a ring $R$ is a [[monomorphism]] $S \xto{m} R$,
that is, an object of the [[poset of subobjects]] $\Sub(G)$. Just as
for [[subgroups]], one can adopt the alternate point of view that a
subring is a special kind of predicate $R \to \prop$.

```agda
Subring : Ring ℓ → Type (lsuc ℓ)
Subring {ℓ = ℓ} = Subobject
```

A predicate $H : G \to \prop$ of a group represents a subring if it
contains $0$ and $1$, and is closed under addition, negation and
multiplication. In other words, it represents both an additive subgroup
and a multiplicative submonoid.
