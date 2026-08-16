<!--
```agda
open import Algebra.Ring
open import 1Lab.Prelude hiding (_*_)

import Algebra.Monoid.Element as Me
import Algebra.Ring.Reasoning as Rr
```
-->

```agda
module Algebra.Ring.Element {ℓ} (R : Ring ℓ) where
```

# Elements of rings

<!--
```agda
open Rr R public

private variable
  x : ⌞ R ⌟
```
-->

In this module we define properties that elements of a ring might have.
Many of these come from the underlying monoid, which are in turn defined
using the [[delooping category]].

```agda
open Me {ℓ} {multiplicative-monoid} public
```

Note that any ring in which 0 is invertible is trivial.

```agda
0-invertible→0≡1 : is-invertible 0r → 0r ≡ 1r
0-invertible→0≡1 0-inv =
    0r                            ≡˘⟨ *-zerol ⟩
    0r * 0-inv .is-invertible.inv ≡⟨ 0-inv .is-invertible.invl ⟩
    1r                            ∎

open is-invertible
open Inverses

neg-invertible : is-invertible x → is-invertible (- x)
neg-invertible {x = x} x-inv = λ where
  .inv → -(x-inv .inv)
  .inverses .invl → *-negatelr ∙ x-inv .inverses .invl
  .inverses .invr → *-negatelr ∙ x-inv .inverses .invr
```
