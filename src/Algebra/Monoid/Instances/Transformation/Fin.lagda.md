<!--
```agda
open import Algebra.Monoid.Instances.Transformation
open import Algebra.Monoid.Cat.Isofibration
open import Algebra.Monoid

open import Cat.Displayed.Isofibration
open import Cat.Displayed.Total
open import Cat.Instances.Sets
open import Cat.Prelude

open import Data.Vec.Properties
open import Data.Product.NAry
open import Data.Fin.Base
open import Data.Vec.Base

import Cat.Reasoning as Cr

open Isofibration (Monoids-isofibration lzero)
```
-->

```agda
module Algebra.Monoid.Instances.Transformation.Fin where
```

<!--
```agda
private module Sets = Cr (Sets lzero)
```
-->

# Finite full transformation monoids {defines="finite-full-transformation-monoid"}

The finite full transformation monoid $\cT_n$ represents the endomaps
of the [[standard finite set]] $\operatorname{Fin}(n)$.

<!--
```agda
module _ (n : Nat) where
  open Monoid-on
```
-->

```agda
  End[n] : Monoid lzero
  End[n] = el! _ , End (el! (Fin n))
```

However, the definition of the [[full transformation monoid]] `End[n]`{.Agda}
on  $\operatorname{Fin}(n)$ has a few disadvantages. Firstly, elements
of `End[n]`{.Agda}, being functions, are awkward to write down. On a
blackboard one often writes an element of $\cT_n$ in the form

$$
a =
\begin{pmatrix}
0 & 1 & 2 & 3 & 4 \\
4 & 1 & 4 & 2 & 1
\end{pmatrix}
: \cT_5.
$$

Here, $a$ is the transformation sending each element in the top row to
the corresponding element in the bottom row. We would like to achieve
something similar in Mikan. Secondly, the product of two elements of
`End[n]`{.Agda} will typically not compute until it is actually applied
to an element of $\operatorname{Fin}(n)$. We would like equal elements
of $\cT_n$ to be _definitionally_ equal whenever possible.

We can solve both these problems using the [[monoids isofibration]] by
transporting the monoid structure on the underlying set of `End[n]`{.Agda}
along the equivalence to the set of [vectors] of length $n$ with
coordinates in $\operatorname{Fin}(n)$.

[vectors]: Data.Vec.Base.html

```agda
  ⌞End⌟≅⌞𝒯⌟ : End[n] .fst Sets.≅ el! (Vec (Fin n) n)
  ⌞End⌟≅⌞𝒯⌟ = equiv→iso $ Equiv.inverse Vec≃Fun

  𝒯 : Monoid lzero
  𝒯 = el! _ , ⌞End⌟≅⌞𝒯⌟ ^* (End[n] .snd)
```

Since the monoid structure on $\cT_n$ was constructed directly from the
monoid structure on `End[n]`{.Agda}, it is clear that these give
isomorphic monoids:

```agda
  End≅𝒯 : End[n] Monoids.≅ 𝒯
  End≅𝒯 = iso[]→total-iso (Monoids-on lzero) (^*-lifts ⌞End⌟≅⌞𝒯⌟ (End[n] .snd))
```

Using [[list syntax for vectors]], the element $a$ above can be written
as

<!--
```agda
module _ where private
  open Monoid-on (𝒯 5 .snd)
```
-->

```agda
  a : ⌞ 𝒯 5 ⌟
  a = [ 4 , 1 , 4 , 2 , 1 ]
```

Moreover, multiplication in $\cT_n$ genuinely computes, so we can write
equations such as

```agda
  _ : a ≡ [ 1 , 2 , 3 , 4 , 0 ] ⋆ [ 3 , 0 , 3 , 1 , 0 ]
  _ = refl
```
