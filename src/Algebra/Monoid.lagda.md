<!--
```agda
open import Algebra.Semigroup
open import Algebra.Magma

open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude

import Cat.Reasoning as Cr
```
-->

```agda
module Algebra.Monoid where
```

<!--
```agda
private variable
  ℓ ℓ₁ : Level
  A B : Type ℓ
```
-->

# Monoids {defines="monoid"}

A **monoid** is a semigroup equipped with a _two-sided identity_
element: An element $e \in M$ such that $e \star x = x = x \star e$. For
any particular choice of binary operator $\star$, if a two-sided
identity exists, then it is unique; In this sense, "being a monoid"
could be considered an "axiom" that semigroups may satisfy.

However, since semigroup homomorphisms do not automatically preserve the
identity element,[^1] it is part of the type signature for
`is-monoid`{.Agda}, being considered _structure_ that a semigroup may be
equipped with.

[^1]: Counterexample: The map $f : (\bb{Z}, *) \to (\bb{Z}, *)$
which sends everything to zero is a semigroup homomorphism, but does not
preserve the unit of $(\bb{Z}, *)$.

```agda
record is-monoid (id : A) (_⋆_ : A → A → A) : Type (level-of A) where
  field
    has-is-semigroup : is-semigroup _⋆_

  open is-semigroup has-is-semigroup public

  field
    idl : {x : A} → id ⋆ x ≡ x
    idr : {x : A} → x ⋆ id ≡ x

open is-monoid
```

The condition of $(A, 0, \star)$ defining a monoid is a proposition, so
that we may safely decompose monoids as the _structure_ $(0, \star)$,
which has to satisfy the _property_ of being a monoid.

```agda
private unquoteDecl eqv = declare-record-iso eqv (quote is-monoid)

instance
  H-Level-is-monoid : ∀ {id : A} {_⋆_ : A → A → A} {n}
                    → H-Level (is-monoid id _⋆_) (suc n)
  H-Level-is-monoid = prop-instance λ x →
    let open is-monoid x in Iso→is-hlevel! 1 eqv x
```

A `monoid structure on`{.Agda ident=Monoid-on} a type is given by the
choice of identity element, the choice of binary operation, and the
witness that these choices form a monoid.

```agda
record Monoid-on (A : Type ℓ) : Type ℓ where
  field
    identity : A
    _⋆_ : A → A → A

    has-is-monoid : is-monoid identity _⋆_

  open is-monoid has-is-monoid public
```

As mentioned above, a monoid homomorphism has to preserve both
multiplication _and_ the identity.

```agda
record is-monoid-hom
  (Aᵐ : Monoid-on A) (Bᵐ : Monoid-on B) (f : A → B)
  : Type (level-of A ⊔ level-of B)
  where
  private
    module A = Monoid-on Aᵐ
    module B = Monoid-on Bᵐ

  field
    pres-id : f A.identity ≡ B.identity
    pres-⋆ : (x y : A) → f (x A.⋆ y) ≡ f x B.⋆ f y
```

<!--
```agda
module _ where
  open Monoid-on
  open is-monoid-hom

  is-monoid-hom-is-prop : ∀ {Aᵐ : Monoid-on A} {Bᵐ : Monoid-on B} {f}
                        → is-prop $ is-monoid-hom Aᵐ Bᵐ f
  is-monoid-hom-is-prop {Bᵐ = Bᵐ} {f} α β i = λ where
    .pres-id → has-is-set Bᵐ _ _ (α .pres-id) (β .pres-id) i
    .pres-⋆ x y → has-is-set Bᵐ _ _ (α .pres-⋆ x y) (β .pres-⋆ x y) i

  instance
    H-Level-monoid-hom
      : ∀ {Aᵐ : Monoid-on A} {Bᵐ : Monoid-on B} {f} {n}
      → H-Level (is-monoid-hom Aᵐ Bᵐ f) (suc n)
    H-Level-monoid-hom = prop-instance is-monoid-hom-is-prop
```
-->

:::{.definition #category-of-monoids}

Monoids and their homomorphisms assemble into a category.

```agda
  Monoid-structure : ∀ ℓ → Thin-structure ℓ Monoid-on
  Monoid-structure _ = λ where
    .is-hom f Aᵐ Bᵐ → el! (is-monoid-hom Aᵐ Bᵐ f)
    .id-is-hom .pres-⋆ _ _ → refl
    .id-is-hom .pres-id → refl
    .∘-is-hom f g fᵐ gᵐ → λ where
      .pres-⋆ x y → ap f (gᵐ .pres-⋆ x y) ∙ fᵐ .pres-⋆ _ _
      .pres-id → (ap f (gᵐ .pres-id)) ∙ fᵐ .pres-id
    .id-hom-unique {s = Aᵐ} {Bᵐ} α β i → λ where
      .identity → α .pres-id i
      ._⋆_ x y → α .pres-⋆ x y i
      .has-is-monoid →
        is-prop→pathp
          (λ i → hlevel {T = is-monoid (α .pres-id i) λ x y → α .pres-⋆ x y i} 1)
          (Aᵐ .has-is-monoid) (Bᵐ .has-is-monoid) i

  instance
    Monoid-equational : ∀ {ℓ} → is-equational (Monoid-structure ℓ)
    Monoid-equational {ℓ = ℓ} .is-equational.invert-id-hom {s = Aᵐ} {Bᵐ} fᵐ = fᵐ⁻¹ where
      fᵐ⁻¹ : is-monoid-hom Bᵐ Aᵐ λ x → x
      fᵐ⁻¹ .pres-id = sym (fᵐ .pres-id)
      fᵐ⁻¹ .pres-⋆ x y = sym (fᵐ .pres-⋆ x y)

  Monoids : ∀ ℓ → Precategory (lsuc ℓ) ℓ
  Monoids ℓ = Structured-objects (Monoid-structure ℓ)
  module Monoids {ℓ} = Cr (Monoids ℓ)

  Monoids-is-category : is-category (Monoids ℓ)
  Monoids-is-category = Structured-objects-is-category _

  Monoid : ∀ ℓ → Type (lsuc ℓ)
  Monoid _ = Monoids.Ob
```

:::

By standard nonsense, then, the category of monoids admits a [[faithful
functor]] into the category of sets.

```agda
Mon↪Sets : ∀ {ℓ} → Functor (Monoids ℓ) (Sets ℓ)
Mon↪Sets = Forget-structure (Monoid-structure _)
```

## Constructing monoids

The interface to `Monoid-on`{.Agda} is contains some annoying nesting,
so we provide an interface that arranges the data in a more user-friendly
way.

```agda
record make-monoid {ℓ} (A : Type ℓ) : Type ℓ where
  field
    monoid-is-set : is-set A
    _⋆_ : A → A → A
    1M : A
    ⋆-assoc : ∀ x y z → x ⋆ (y ⋆ z) ≡ (x ⋆ y) ⋆ z
    ⋆-idl : ∀ x → 1M ⋆ x ≡ x
    ⋆-idr : ∀ x → x ⋆ 1M ≡ x

  to-is-monoid : is-monoid 1M _⋆_
  to-is-monoid .has-is-semigroup .is-semigroup.has-is-magma = record { has-is-set = monoid-is-set }
  to-is-monoid .has-is-semigroup .is-semigroup.associative = ⋆-assoc _ _ _
  to-is-monoid .idl = ⋆-idl _
  to-is-monoid .idr = ⋆-idr _

  to-monoid-on : Monoid-on A
  to-monoid-on .Monoid-on.identity = 1M
  to-monoid-on .Monoid-on._⋆_ = _⋆_
  to-monoid-on .Monoid-on.has-is-monoid = to-is-monoid

open make-monoid using (to-is-monoid; to-monoid-on) public
```

Given an equivalence $e : A \simeq B$, we can transport a monoid
structure on $A$ to one on $B$ so that $e$ becomes a homomorphism.

```agda
module _ (e : A ≃ B) (mA : Monoid-on A) where
  open make-monoid
  open is-monoid-hom
  open Equiv e
  private module mA = Monoid-on mA

  monoid-transport : Monoid-on B
  monoid-transport = to-monoid-on m where
    m : make-monoid B
    m .monoid-is-set = Equiv→is-hlevel 2 inverse mA.has-is-set
    m ._⋆_ x y = to (from x mA.⋆ from y)
    m .1M = to mA.identity
    m .⋆-assoc x y z =
      to (from x mA.⋆ ⌜ from (to (from y mA.⋆ from z)) ⌝) ≡⟨ ap! (η _) ⟩
      to (from x mA.⋆ (from y mA.⋆ from z))               ≡⟨ ap to mA.associative ⟩
      to (⌜ from x mA.⋆ from y ⌝ mA.⋆ from z)             ≡˘⟨ ap¡ (η _) ⟩
      to (from (to (from x mA.⋆ from y)) mA.⋆ from z)     ∎
    m .⋆-idl x =
      to (⌜ from (to mA.identity) ⌝ mA.⋆ from x)  ≡⟨ ap! (η _) ⟩
      to (mA.identity mA.⋆ from x)                ≡⟨ ap to mA.idl ⟩
      to (from x)                                 ≡⟨ ε _ ⟩
      x                                           ∎
    m .⋆-idr x =
      to (from x mA.⋆ ⌜ from (to mA.identity) ⌝)  ≡⟨ ap! (η _) ⟩
      to (from x mA.⋆ mA.identity)                ≡⟨ ap to mA.idr ⟩
      to (from x)                                 ≡⟨ ε _ ⟩
      x                                           ∎

  monoid-transport-hom : is-monoid-hom mA monoid-transport to
  monoid-transport-hom .pres-id = refl
  monoid-transport-hom .pres-⋆ x y =
    to (⌜ x ⌝ mA.⋆ y)                 ≡˘⟨ ap¡ (η _) ⟩
    to (from (to x) mA.⋆ ⌜ y ⌝)       ≡˘⟨ ap¡ (η _) ⟩
    to (from (to x) mA.⋆ from (to y)) ∎
```

Monoids of a given universe level and their morphisms are assembled into
the [[category of monoids]].

## Relationships to unital magmas

```agda
open import Algebra.Magma.Unital
```

By definition, every monoid is exactly a `unital magma`{.Agda ident=is-unital-magma}
that is also a `semigroup`{.Agda ident=is-semigroup}. However, adopting
this as a definition yields several issues especially when it comes to
metaprogramming, which is why this is instead expressed by explicitly
proving the implications between the properties.

First, we show that every monoid is a unital magma:

```agda
module _ {id : A} {_⋆_ : A → A → A} where
  is-monoid→is-unital-magma : is-monoid id _⋆_ → is-unital-magma id _⋆_
  is-monoid→is-unital-magma mon .has-is-magma = mon .has-is-magma
  is-monoid→is-unital-magma mon .idl = mon .idl
  is-monoid→is-unital-magma mon .idr = mon .idr
```

"Reshuffling" the record fields also allows us to show the reverse
direction, namely, that every unital semigroup is a monoid.

```agda
  is-unital-magma→is-semigroup→is-monoid
    : is-unital-magma id _⋆_ → is-semigroup _⋆_ → is-monoid id _⋆_
  is-unital-magma→is-semigroup→is-monoid uni sem .has-is-semigroup = sem
  is-unital-magma→is-semigroup→is-monoid uni sem .idl = uni .idl
  is-unital-magma→is-semigroup→is-monoid uni sem .idr = uni .idr
```

## Inverses

A useful application of the monoid laws is in showing that _having an
**inverse**_ is a _property_ of a specific element, not structure on
that element. To make this precise: Let $e$ be an element of a monoid,
say $(M, 1, \star)$; If there are $x$ and $y$ such that $x \star e = 1$
and $e \star y = 1$, then $x = y$.

```agda
monoid-inverse-unique
  : ∀ {1M : A} {_⋆_ : A → A → A}
  → (m : is-monoid 1M _⋆_)
  → (e x y : A)
  → (x ⋆ e ≡ 1M) → (e ⋆ y ≡ 1M)
  → x ≡ y
```

This is a happy theorem where stating the assumptions takes as many
lines as the proof, which is a rather boring calculation. Since $1$ is
an identity for $\star$, we can freely multiply by $1$ to "sneak in" a
$y$:

```agda
monoid-inverse-unique {1M = 1M} {_⋆_} m e x y li1 ri2 =
  x             ≡⟨ sym (m .idr) ⟩
  x ⋆ ⌜ 1M ⌝    ≡˘⟨ ap¡ ri2 ⟩
  x ⋆ (e ⋆ y)   ≡⟨ m .associative ⟩
  ⌜ x ⋆ e ⌝ ⋆ y ≡⟨ ap! li1 ⟩
  1M ⋆ y        ≡⟨ m .idl ⟩
  y             ∎
```
