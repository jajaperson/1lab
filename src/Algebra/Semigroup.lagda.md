<!--
```agda
open import Algebra.Magma

open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude hiding (Nat-is-set)

import Cat.Reasoning as Cr
```
-->

```agda
module Algebra.Semigroup where
```

<!--
```agda
private variable
  ℓ ℓ₁ : Level
  A B : Type ℓ
```
-->

# Semigroups {defines=semigroup}

```agda
record is-semigroup {A : Type ℓ} (_⋆_ : A → A → A) : Type ℓ where
```

A **semigroup** is an associative `magma`{.Agda ident=is-magma}, that is, a set
equipped with a choice of _associative_ binary operation `⋆`.

```agda
  field
    has-is-magma : is-magma _⋆_
    associative : {x y z : A} → x ⋆ (y ⋆ z) ≡ (x ⋆ y) ⋆ z

  open is-magma has-is-magma public
```

To see why the [[set truncation]] is really necessary, it helps to
explicitly describe the expected structure of a "∞-semigroup" in terms
of the language of higher categories:

- An ∞-groupoid `A`, equipped with

- A map `_⋆_ : A → A → A`, such that

- `⋆` is _associative_: there exists an invertible 2-morphism `α : A ⋆
(B ⋆ C) ≡ (A ⋆ B) ⋆ C` (called the associator), satisfying

- The _pentagon identity_, i.e. there is a path `π` (called, no joke,
the "pentagonator") witnessing commutativity of the diagram below, where
all the faces are `α`:

~~~{.quiver}
\[\begin{tikzcd}
  & {(a \star b) \star (c\star d)} \\
  {((a \star b) \star c)\star d} && {a\star(b\star(c\star d)))} \\
  \\
  {(a\star(b\star c))\star d} && {a\star((b\star c)\star d)}
  \arrow[Rightarrow, no head, from=2-1, to=1-2]
  \arrow[Rightarrow, no head, from=1-2, to=2-3]
  \arrow[Rightarrow, no head, from=2-3, to=4-3]
  \arrow[Rightarrow, no head, from=4-3, to=4-1]
  \arrow[Rightarrow, no head, from=4-1, to=2-1]
\end{tikzcd}\]
~~~

- The pentagonator satisfies its own coherence law, which looks like the
Stasheff polytope $K_5$, and so on, "all the way up to infinity".

By explicitly asking that `A` be truncated at the level of sets, we have
that the associator automatically satisfies the pentagon identity -
because all parallel paths in a set are equal. Furthermore, by the
upwards closure of h-levels, any further coherence condition you could
dream up and write down for these morphisms is automatically satisfied.

As a consequence of this truncation, we get that being a semigroup
operator is a _property_ of the operator:

```agda
is-semigroup-is-prop : {_⋆_ : A → A → A} → is-prop (is-semigroup _⋆_)
is-semigroup-is-prop x y i .is-semigroup.has-is-magma =
  is-magma-is-prop (x .is-semigroup.has-is-magma) (y .is-semigroup.has-is-magma) i
is-semigroup-is-prop {_⋆_ = _⋆_} x y i .is-semigroup.associative {a} {b} {c} =
  x .is-semigroup.has-is-set (a ⋆ (b ⋆ c)) ((a ⋆ b) ⋆ c)
    (x .is-semigroup.associative) (y .is-semigroup.associative) i

instance
  H-Level-is-semigroup : ∀ {_*_ : A → A → A} {n} → H-Level (is-semigroup _*_) (suc n)
  H-Level-is-semigroup = prop-instance is-semigroup-is-prop
```

A **semigroup structure on** a type packages up the binary operation and
the axiom in a way equivalent to a `structure`{.Agda ident=Structure}.

```agda
record Semigroup-on (A : Type ℓ) : Type ℓ where
  field
    _⋆_ : A → A → A

    has-is-semigroup : is-semigroup _⋆_

  open is-semigroup has-is-semigroup public

  has-Magma-on : Magma-on A
  has-Magma-on = record { _⋆_ = _⋆_ ; has-is-magma = has-is-magma }

open Semigroup-on using (has-Magma-on)
```

A semigroup homomorphism is just a homomorphism of the underlying
[[magmas]]

```agda
is-semigroup-hom
  : (Aˢ : Semigroup-on A) (Bˢ : Semigroup-on B) (f : A → B)
  → Type (level-of A ⊔ level-of B)
is-semigroup-hom Aˢ Bˢ = is-magma-hom (has-Magma-on Aˢ) (has-Magma-on Bˢ)
```

<!--
```agda
is-semigroup-hom-is-prop : ∀ (Aˢ : Semigroup-on A) (Bˢ : Semigroup-on B) f
                         → is-prop (is-semigroup-hom Aˢ Bˢ f)
is-semigroup-hom-is-prop Aˢ Bˢ f = is-magma-hom-is-prop (has-Magma-on Aˢ) (has-Magma-on Bˢ) f

module _ where
  open Semigroup-on
```
-->

Semigroups and their homomorphisms assemble into a category.

```agda
  Semigroup-structure : ∀ ℓ → Thin-structure ℓ Semigroup-on
  Semigroup-structure ℓ = λ where
    .is-hom f Aˢ Bˢ → el (is-semigroup-hom Aˢ Bˢ f) (is-semigroup-hom-is-prop Aˢ Bˢ f)
    .id-is-hom _ _ → refl
    .∘-is-hom f g fˢ gˢ x y → ap f (gˢ x y) ∙ fˢ _ _
    .id-hom-unique α _ i ._⋆_ x y → α x y i
    .id-hom-unique {s = Aˢ} {Bˢ} α _ i .has-is-semigroup →
      is-prop→pathp
        (λ i → is-semigroup-is-prop {_⋆_ = λ x y → α x y i})
        (Aˢ .has-is-semigroup) (Bˢ .has-is-semigroup) i

  Semigroups : ∀ ℓ → Precategory (lsuc ℓ) ℓ
  Semigroups ℓ = Structured-objects (Semigroup-structure ℓ)
  module Semigroups {ℓ} = Cr (Semigroups ℓ)

  Semigroups-is-category : is-category (Semigroups ℓ)
  Semigroups-is-category = Structured-objects-is-category (Semigroup-structure _)

  Semigroup : ∀ ℓ → Type (lsuc ℓ)
  Semigroup _ = Semigroups.Ob
```

## The "min" semigroup

An example of a naturally-occurring semigroup are the natural numbers
under taking `minimums`{.Agda ident=min}.

```agda
open import Data.Nat.Properties
open import Data.Nat.Order
open import Data.Nat.Base

open is-semigroup

Nat-min : is-semigroup min
Nat-min .has-is-magma .is-magma.has-is-set = Nat-is-set
Nat-min .associative = min-assoc _ _ _
```

What is meant by "naturally occurring" is that this semigroup can not be
made into a monoid: There is no natural number `unit` such that, for all
`y`, `min unit y ≡ y` and `min y unit ≡ y`.

```agda
private
  min-no-id : (unit : Nat) → ¬ ((y : Nat) → min unit y ≡ y)
  min-no-id x id =
    let
      sucx≤x : suc x ≤ x
      sucx≤x = subst (λ e → e ≤ x) (id (suc x)) (min-≤l x (suc x))
    in ¬sucx≤x x sucx≤x
```

# Constructing semigroups

The interface to `Semigroup-on`{.Agda} is contains some annoying nesting,
so we provide an interface that arranges the data in a more user-friendly
way.

```agda
record make-semigroup {ℓ} (A : Type ℓ) : Type ℓ where
  field
    semigroup-is-set : is-set A
    _⋆_ : A → A → A
    ⋆-assoc : ∀ x y z → x ⋆ (y ⋆ z) ≡ (x ⋆ y) ⋆ z

  to-is-semigroup : is-semigroup _⋆_
  to-is-semigroup .has-is-magma .is-magma.has-is-set = semigroup-is-set
  to-is-semigroup .associative = ⋆-assoc _ _ _

  to-semigroup-on : Semigroup-on A
  to-semigroup-on .Semigroup-on._⋆_ = _⋆_
  to-semigroup-on .Semigroup-on.has-is-semigroup = to-is-semigroup

  to-semigroup : Semigroup ℓ
  to-semigroup = el A semigroup-is-set , to-semigroup-on

open make-semigroup using (to-is-semigroup; to-semigroup-on) public
```
