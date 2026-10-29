<!--
```agda
--
open import 1Lab.Prelude

open import Algebra.Group
open import Algebra.Ring

open import Data.Fin.Arithmetic
open import Data.Fin.Base
open import Data.Int.Base hiding (Positive)
open import Data.Nat.Base

import Algebra.Ring.Reasoning as Rr
```
-->

```agda
module Algebra.Ring.Instances.Int.Quotients where
```

# Rings of integers modulo $n$

```
ℤ/⟨_⟩ : ∀ n ⦃ _ : Positive n ⦄ → Ring lzero
ℤ/⟨ n ⟩ = to-ring {R = Fin n} record
  { ring-is-set = hlevel 2
  ; 0R = 0
  ; _+_ = _+ₘ_
  ; -_ = -ₘ_
  ; +-idl = +ₘ-zerol
  ; +-invr = +ₘ-invr
  ; +-assoc = +ₘ-associative
  ; +-comm = +ₘ-commutative
  ; 1R = 1ₘ
  ; _*_ = _*ₘ_
  ; *-idl = *ₘ-onel
  ; *-idr = *ₘ-oner
  ; *-assoc = *ₘ-associative
  ; *-distribl = *ₘ-distrib-+ₘl
  ; *-distribr = *ₘ-distrib-+ₘr
  }
   
module _ {n} ⦃ _ : Positive n ⦄ where
  private
    ℤₙ = ℤ/⟨ n ⟩
    module ℤₙ = Rr ℤₙ

    e : Nat → Fin n
    e = _%ᶠ n

  [_] : Int → Fin n
  [ pos x ] = e x
  [ negsuc x ] = -ₘ e (suc x)
```
