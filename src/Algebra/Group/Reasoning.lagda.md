```agda
open import 1Lab.Prelude hiding (_*_)

open import Algebra.Group.Notation
open import Algebra.Group.Solver
open import Algebra.Group

module Algebra.Group.Reasoning {ℓ} {G : Type ℓ} (Gᵍ : Group-on G) where
```

# Reasoning combinators for groups

<!--
```agda
open Multiplicative-notation Gᵍ

private variable
  x y z : G
```
-->

```agda
inverse-diff : (x * y ⁻¹) ⁻¹ ≡ y * x ⁻¹
inverse-diff = group-on! Gᵍ

diff≡diff*diff : x * z ⁻¹ ≡ (x * y ⁻¹) * (y * z ⁻¹)
diff≡diff*diff = group-on! Gᵍ
```
