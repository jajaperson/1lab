<!--
```agda
open import 1Lab.Univalence.SIP
open import 1Lab.Prelude
```
-->

```agda
module Homotopy.InftyMagma where
```

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
```
-->

# ∞-Magmas {defines="∞-magma"}

In common mathematical parlance, a **magma** is a set equipped with a
binary operation. In HoTT, we free ourselves from considering sets as a
primitive, and generalise to ∞-groupoids: An **∞-magma** is a _type_
equipped with a binary operation.

```agda
∞Magma-on : Type ℓ → Type ℓ
∞Magma-on X = X → X → X
```

Since we can canonically identify the type `∞Magma-on`{.Agda} with a
`Structure`{.Agda} built with the structure language, we automatically
get a notion of ∞-Magma homomorphism, and a proof that `∞MagmaStr`{.Agda}
is a `univalent structure`{.Agda ident=is-univalent}.

```agda
∞MagmaStr : Structure ℓ ∞Magma-on
∞MagmaStr = Term→structure (s∙ s→ (s∙ s→ s∙))

∞MagmaStr-univ : is-univalent (∞MagmaStr {ℓ = ℓ})
∞MagmaStr-univ = Term→structure-univalent (s∙ s→ (s∙ s→ s∙))
```

∞-magmas form a viable structure because magmas (and therefore their
higher version) do not axiomatize any _paths_ that would require
further coherence conditions. However, when considering structures with
equalities, like [[semigroups]], we must restrict ourselves to sets
to get a reasonable object. Hence we define ordinary [[magmas]] in a
separate module as ∞-magmas whose carriers are sets.
