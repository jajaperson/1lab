<!--
```agda
open import Algebra.Ring.Instances.Localisation
open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring

open import Data.Set.Coequaliser hiding (_/_)

open import 1Lab.Prelude hiding (_*_)

import Algebra.Ring.Element as Re
```
-->

```agda
module Algebra.Ring.Instances.Localisation.Element
  {ℓ} {R : CRing ℓ} (S : ⌞ R ⌟ → Ω) (mult : Frac.is-multiplicative R (_∈ S))
  where
```

# Elements of localisations of commutative rings

<!--
```agda
open Frac.is-multiplicative mult
open Loc R S mult
open CRing S⁻¹R using () renaming (ring to L)
private module L where
  open CRing S⁻¹R using (*-commutes) public
  open Re L public
  open Ring-on (L .snd) public

open Fraction renaming (num to ↑ ; denom to ↓)

open CRing R
```
-->

Let $R$ be a commutative ring, $S$ be a set of elements, and consider
the [[localisation|localisation of a commutative ring]] $L := R[S\inv]$.
By construction, if $x \in S$, then $x / 1$ is invertible $L$.

```agda
/1-invertible : ∀ x (p : x ∈ S) → L.is-invertible (x /1)
/1-invertible x p = L.make-invertible
  (inc (1r / x [ p ]))
  (L.*-commutes {x = x /1} {y = inc (1r / x [ p ])} ∙ /1-inverts x p)
  (/1-inverts x p)

/1-unit : ∀ x (p : x ∈ S) → L.Unit
/1-unit x p = L.invertible→unit (x /1) (/1-invertible x p)
```

On the other hand, a general fraction is invertible if the numerator is
invertible.

```agda
split-fraction : ∀ a → inc a ≡ ↑ a /1 *ₗ inc (1r / ↓ a [ has-denom a ])
split-fraction a = ap Coeq.inc (Fraction-path (sym *-idr) (sym *-idl))

/-invertible : ∀ a → L.is-invertible ((↑ a) /1) → L.is-invertible (inc a)
/-invertible a ↑a-inv = subst L.is-invertible (sym (split-fraction a)) $
  L.invertible-* ↑a-inv ((/1-invertible (↓ a) (has-denom a)) L.invertible⁻¹)
```

Any fraction with numerator zero is equal to zero

```agda
num≡0 : ∀ a → ↑ a ≡ 0r → inc a ≡ L.0r
num≡0 a ↑a≡0 = quot (Frac.inc 1r has-1 (
  1r * ⌜ ↑ a ⌝ * 1r ≡⟨ ap! ↑a≡0 ⟩
  1r * 0r * 1r      ≡⟨ cring! R ⟩
  1r * 0r * ↓ a  ∎
  ))
```
