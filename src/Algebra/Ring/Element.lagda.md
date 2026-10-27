<!--
```agda
open import Algebra.Ring.Commutative
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
open Ring-on (R .snd) using (has-is-group)
open Rr R

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

Note that any ring in which 0 is monic or epic is trivial.

```agda
0-monic→0≡1 : is-monic 0r → 0r ≡ 1r
0-monic→0≡1 0-monic = 0-monic 0r 1r $ *-zerol ∙ sym (*-zerol)

0-epic→0≡1 : is-epic 0r → 0r ≡ 1r
0-epic→0≡1 0-epic = 0-epic 0r 1r $ *-zeror ∙ sym (*-zeror)

0-cancellable→0≡1 : is-cancellable 0r → 0r ≡ 1r
0-cancellable→0≡1 = 0-monic→0≡1 ∘ fst

0-invertible→0≡1 : is-invertible 0r → 0r ≡ 1r
0-invertible→0≡1 = 0-monic→0≡1 ∘ invertible→monic

open is-invertible
open Inverses

neg-invertible : is-invertible x → is-invertible (- x)
neg-invertible {x} x-inv = λ where
  .inv → -(x-inv .inv)
  .inverses .invl → *-negatelr ∙ x-inv .inverses .invl
  .inverses .invr → *-negatelr ∙ x-inv .inverses .invr

neg-cancellable : is-cancellable x → is-cancellable (- x)
neg-cancellable {x} (x-monic , x-epic) = -x-monic , -x-epic where
  module - = Equiv (_ , inv-is-equiv)

  -x-monic : is-monic (- x)
  -x-monic a b p = x-monic a b $ -.injective $ sym *-negatel ∙∙ p ∙∙ *-negatel
  
  -x-epic : is-epic (- x)
  -x-epic a b p = x-epic a b $ -.injective $ sym *-negater ∙∙ p ∙∙ *-negater
```

