<!--
```agda
open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Properties
open import Cat.Univalent
open import Cat.Prelude

import Cat.Reasoning as Cr
```
-->

```agda
module Algebra.Magma where
```

<!--
```agda
private variable
  ℓ ℓ₁ : Level
  A B : Type ℓ
```
-->

# Magmas {defines="magma"}

A **magma** is a `set`{.Agda ident=is-set} equipped with an arbitrary
binary operation `⋆`, on which no further laws are imposed.

```agda
record is-magma {A : Type ℓ} (_⋆_ : A → A → A) : Type ℓ where
  field
    has-is-set : is-set A

  underlying-set : Set ℓ
  underlying-set = el _ has-is-set

  opaque instance
    magma-hlevel : ∀ {n} → H-Level A (2 + n)
    magma-hlevel = basic-instance 2 has-is-set

open is-magma
```

Note that we do not generally benefit from the [[set truncation]] of
arbitrary magmas — see [[∞-magmas]] — however, practically all
structures built upon `is-magma`{.Agda} do, since they contain paths
which would require complicated, if not outright undefinable, coherence
conditions.

<!--
```agda
is-magma-is-prop : {_⋆_ : A → A → A} → is-prop (is-magma _⋆_)
is-magma-is-prop x y i .has-is-set =
  is-hlevel-is-prop 2 (x .has-is-set) (y .has-is-set) i

instance
  H-Level-is-magma
    : ∀ {ℓ} {A : Type ℓ} {_⋆_ : A → A → A} {n}
    → H-Level (is-magma _⋆_) (suc n)
  H-Level-is-magma = prop-instance is-magma-is-prop
```
-->

By turning the operation parameter into an additional piece of data, we
get the notion of a **magma structure** on a type, as well as the
notion of a magma in general by doing the same to the carrier type.

```agda
record Magma-on (A : Type ℓ) : Type ℓ where
  field
    _⋆_ : A → A → A

    has-is-magma : is-magma _⋆_

  open is-magma has-is-magma public
```

A magma homomorphism is a map preserving the binary operation.

```agda
is-magma-hom
  : (Aᵐ : Magma-on A) (Bᵐ : Magma-on B) (f : A → B)
  → Type (level-of A ⊔ level-of B)
is-magma-hom Aᵐ Bᵐ f = ∀ x y → f (x A.⋆ y) ≡ f x B.⋆ f y where
  module A = Magma-on Aᵐ
  module B = Magma-on Bᵐ
```

<!--
```agda
is-magma-hom-is-prop : ∀ (Aᵐ : Magma-on A) (Bᵐ : Magma-on B) f
                     → is-prop (is-magma-hom Aᵐ Bᵐ f)
is-magma-hom-is-prop _ Bᵐ _ a b i x y = Magma-on.has-is-set Bᵐ _ _ (a x y) (b x y) i

open Magma-on
```
-->

It follows that magmas and their homomorphisms assemble into a category.

```agda
Magma-structure : ∀ ℓ → Thin-structure ℓ Magma-on
Magma-structure ℓ .is-hom f Aᵐ Bᵐ = el (is-magma-hom Aᵐ Bᵐ f) (is-magma-hom-is-prop Aᵐ Bᵐ f)
Magma-structure ℓ .id-is-hom _ _ = refl
Magma-structure ℓ .∘-is-hom f g fᵐ gᵐ x y = (ap f (gᵐ x y)) ∙ (fᵐ (g x) (g y))
Magma-structure ℓ .id-hom-unique α _ i ._⋆_ x y = α x y i
Magma-structure ℓ .id-hom-unique {s = s} {t} α _ i .has-is-magma =
  is-prop→pathp
    (λ i → is-magma-is-prop {_⋆_ = λ x y → α x y i})
    (s .has-is-magma) (t .has-is-magma) i

Magmas : ∀ ℓ → Precategory  (lsuc ℓ) ℓ
Magmas _ = Structured-objects (Magma-structure _)
module Magmas {ℓ} = Cr (Magmas ℓ)

Magmas-is-category : is-category (Magmas ℓ)
Magmas-is-category = Structured-objects-is-category (Magma-structure _)

Magma : ∀ ℓ → Type (lsuc ℓ)
Magma ℓ = Magmas.Ob
```

By standard nonsense, there is a forgetful functor taking magmas to
their underlying sets

```agda
Magmas↪Sets : Functor (Magmas ℓ) (Sets ℓ)
Magmas↪Sets = Forget-structure (Magma-structure _)

Magmas↪Sets-is-faithful : is-faithful (Magmas↪Sets {ℓ})
Magmas↪Sets-is-faithful = Structured-hom-path (Magma-structure _)
```

## The boolean implication magma

```agda
open import Data.Bool
```

To give a somewhat natural example for a magma that is neither
associative, commutative, nor has a two-sided identity element,
consider `boolean implication`{.Agda imp}. Since the booleans form a
set, this obviously defines a magma:

```agda
private
  is-magma-imp : is-magma imp
  is-magma-imp .has-is-set = hlevel 2
```

We show it is not commutative or associative by giving counterexamples:

```agda
  imp-not-commutative : ¬ ((x y : Bool) → imp x y ≡ imp y x)
  imp-not-commutative commutative = true≠false (commutative false true)

  imp-not-associative : ¬ ((x y z : Bool) → imp x (imp y z) ≡ imp (imp x y) z)
  imp-not-associative associative = true≠false (associative false false false)
```

It also has no two-sided unit, as can be shown by case-splitting
on the candidates:

```agda
  imp-not-unital
    : (x : Bool) → ((y : Bool) → imp x y ≡ y) → ¬ ((y : Bool) → imp y x ≡ y)
  imp-not-unital false left-unital right-unital = true≠false (right-unital false)
  imp-not-unital true left-unital right-unital = true≠false (right-unital false)
```
