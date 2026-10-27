<!--
```agda
open import Algebra.Ring.Cancellative
open import Algebra.Ring.Commutative renaming (ℤ-comm to ℤ)
open import Algebra.Ring.Commutative.Element ℤ

open import Data.Int
open import Data.Nat.Base
open import Data.Dec.Base
open import Data.Sum

open import 1Lab.Prelude
```
-->

```
module Algebra.Ring.Instances.Int.Properties where
```

# Properties of the ring of integers

## $\ZZ$ is a discrete integral domain

```agda
open is-discrete-cancellative

ℤ-is-DID : is-discrete-integral-domain ℤ
ℤ-is-DID .0≠1 = zero≠suc ∘ pos-injective
ℤ-is-DID .cancellable? x with x ≡? 0
... | yes x≡0 = inr x≡0
... | no x≠0 = inl (epic→cancellable λ a b ax≡bx → *ℤ-injectiver x a b x≠0 ax≡bx)
```
