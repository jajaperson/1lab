<!--
```agda
open import 1Lab.Reflection hiding (absurd)
open import 1Lab.Prelude

open import Data.Set.Coequaliser
open import Data.Dec.Base
open import Data.Sum

open import Homotopy.Join
```
-->

```agda
module Data.Set.Apartness where
```

<!--
```agda
private variable
  ℓ ℓ# ℓ#' : Level
  A B : Type ℓ
  R : A → A → Type ℓ#
```
-->

# Apartness relations {defines="apartness-relation"}

An **apartness relation** on a type $A$ is a (mere) relation $\apt$ on
$A$ satisfying properties that are in some sense complementary to a
[[congruence]]: it is _irreflexive_, _cotransitive_, and _symmetric_.

```agda
record is-apartness (_#_ : A → A → Type ℓ#) : Type (level-of A ⊔ ℓ#) where
  no-eta-equality
  field
    has-is-prop : ∀ {x y} → is-prop (x # y)
    irrefl : ∀ {x} → ¬(x # x)
    cotrans : ∀ {x y z} → x # z → (x # y) ∗ (y # z)
    symᵃ : ∀ {x y} → x # y → y # x

  irrefl' : ∀ {x y} → x ≡ y → ¬(x # y)
  irrefl' {x} x≡y = subst (λ y → ¬(x # y)) x≡y irrefl

record Apartness {ℓ} (A : Type ℓ) ℓ# : Type (ℓ ⊔ lsuc ℓ#) where
  field
    _#_ : A → A → Type ℓ#
    has-is-apartness : is-apartness _#_

  open is-apartness has-is-apartness public
```

<!--
```agda
to-apartness : ∀ {_#_ : A → A → Type ℓ#} → is-apartness _#_ → Apartness A ℓ#
to-apartness {_#_ = _#_} apt = record { _#_ = _#_ ; has-is-apartness = apt }

private unquoteDecl apt-eqv = declare-record-iso apt-eqv (quote is-apartness)

instance
  H-Level-is-apartness
    : ∀ {_#_ : A → A → Type ℓ#} {n}
    → H-Level (is-apartness _#_) (suc n)
  H-Level-is-apartness {_#_ = _#_} = prop-instance λ x →
    let
      open is-apartness x
      instance
        ha : ∀ {k x y} → H-Level (x # y) (suc k)
        ha = prop-instance has-is-prop
        hj : ∀ {k x y z} → H-Level ((x # y) ∗ (y # z)) (suc k)
        hj = prop-instance (join-is-prop has-is-prop has-is-prop)
    in Iso→is-hlevel! 1 apt-eqv x
```
-->

The complement of an apartness relation on $A$ is a congruence on $A$.

```agda
Apartness→Congruence : Apartness A ℓ# → Congruence A ℓ#
Apartness→Congruence apt = record where
  open Apartness apt
  _∼_ x y = ¬(x # y)
  has-is-prop x y = hlevel 1
  reflᶜ = irrefl
  _∙ᶜ_ x∼y y∼z x#z = join-elim-prop (λ _ ()) (λ ()) (λ ()) $
    join-map x∼y y∼z (cotrans x#z)
  symᶜ = _∘ symᵃ
```

## Tight apartness relations {defines="tight-apartness-relation aset"}

In most cases of interest, $X$ is a set and the complementary congruence
relation is equality. An apartness relation with this property is called
**tight**, and a type equipped with such an apartness relation is called
an **aset**.

```
is-tight : ∀ (_#_ : A → A → Type ℓ#) → Type (level-of A ⊔ ℓ#)
is-tight _#_ = ∀ {x y} → ¬(x # y) → x ≡ y

record Tight-apartness {ℓ} (A : Type ℓ) ℓ# : Type (ℓ ⊔ lsuc ℓ#) where
  field
    apartness : Apartness A ℓ#

  open Apartness apartness public

  field
    tight : is-tight _#_
```

An aset has $\neg\neg$-stable equality, and thus is automatically a set
by [[Hedberg's theorem]].

```agda
  ¬¬-stable-≡ : ∀ {x y : A} → ¬ ¬ (x ≡ y) → x ≡ y
  ¬¬-stable-≡ {x} {y} ¬¬x≡y = tight λ x#y → ¬¬x≡y λ x≡y → irrefl' x≡y x#y

  has-is-set : is-set A
  has-is-set = identity-system→hlevel 1
    (¬¬-stable-identity-system ¬¬-stable-≡)
    λ x y f g → funext λ z → absurd (g z)

  tight-is-equiv : ∀ {x y} → is-equiv (tight {x} {y})
  tight-is-equiv {x} {y} = biimp-is-equiv (hlevel 1) (has-is-set x y) tight
    λ x≡y x#y → irrefl' x≡y x#y

  module tight {x y} = Equiv (_ , tight-is-equiv {x} {y})
```

## Stable and decidable tight apartness relations

A $\neg\neg$-stable tight apartness relation is logically equivalent to
denial inequality.

```agda
  is-stable : Type (level-of A ⊔ ℓ#)
  is-stable = ∀ {x y} → ¬ ¬(x # y) → x # y

  is-stable→#≃≠ : is-stable → ∀ {x y} → (x # y) ≃ (x ≠ y)
  is-stable→#≃≠ stable = prop-ext has-is-prop (hlevel 1)
    (λ x#y x≡y → irrefl' x≡y x#y)
    λ x≠y → stable (x≠y ∘ tight)
```

Decidable tight apartness relations allow us to determine whether any
two elements are apart or equal.

```agda
  is-decidable : Type (level-of A ⊔ ℓ#)
  is-decidable = ∀ x y → (x # y) ⊎ (x ≡ y)


  decidable→Dec : is-decidable → ∀ x y → Dec (x # y)
  decidable→Dec dec x y with dec x y
  ...                      | inl x#y = yes x#y
  ...                      | inr x≡y = no (irrefl' x≡y)

  decidable→stable : is-decidable → is-stable
  decidable→stable dec = dec→dne ⦃ decidable→Dec dec _ _ ⦄
```

In particular $A$ is a [[discrete]] set, then denial inequality is a
decidable tight apartness relation.

<!--
```agda
module _ {A : Type ℓ} (disc : Discrete A) where
  instance Dec-Path-A = disc
```
-->

```agda
  discrete→≠-is-apartness : is-apartness (_≠_ {A = A})
  discrete→≠-is-apartness = record where
    irrefl x≠x = x≠x refl
    symᵃ x≠y y≡x = x≠y (sym y≡x)
    cotrans {x} {y} {z} x≠z = caseᵈ (x ≡ y) of λ where
      (yes x≡y) → inr λ y≡z → x≠z (x≡y ∙ y≡z)
      (no x≠z) → inl x≠z
    has-is-prop = hlevel 1

  discrete→≠-is-tight : is-tight (_≠_ {A = A})
  discrete→≠-is-tight = dec→dne

  discrete→aset : Tight-apartness A ℓ
  discrete→aset = record where
    apartness = record where
      _#_ = _≠_
      has-is-apartness = discrete→≠-is-apartness
    tight = discrete→≠-is-tight

  discrete→≠-is-decidable : Tight-apartness.is-decidable discrete→aset
  discrete→≠-is-decidable x y = caseᵈ (x ≡ y) of λ where
    (yes x≡y) → inr x≡y
    (no x≠y)  → inl x≠y
```

<!--
```agda
to-tight-apartness
  : {_#_ : A → A → Type ℓ#} → is-apartness _#_ → is-tight _#_
  → Tight-apartness A ℓ#
to-tight-apartness {_#_ = _#_} apt tight = record
  { apartness = record { _#_ = _#_ ; has-is-apartness = apt }
  ; tight = tight
  }
```
-->

## Strongly extensional functions {defines="strongly-extensional-function"}

<!--
```agda
module _ (Aᵃ : Tight-apartness A ℓ#) (Bᵃ : Tight-apartness B ℓ#') where
  private
    module A = Tight-apartness Aᵃ
    module B = Tight-apartness Bᵃ
```
-->

Let $A$ and $B$ be asets. A function $f : A \to B$ is said to be
**strongly extensional** iff it reflects apartness in the following
sense:

```agda
  is-strongly-ext : (A → B) → Type (ℓ# ⊔ ℓ#' ⊔ level-of A)
  is-strongly-ext f = ∀ {x y} → (f x) B.# (f y) → x A.# y
```


:::{.definition #strong-injection alias="strongly-injective"}
Similarly, a function is said to be **strongly injective** iff it
preserves apartness.

```agda
  is-strongly-inj : (A → B) → Type (ℓ# ⊔ ℓ#' ⊔ level-of A)
  is-strongly-inj f = ∀ {x y} → x A.# y → (f x) B.# (f y)
```
:::

As the name suggests, being strongly injective implies being injective.

```agda
  strongly-inj→inj : ∀ f → is-strongly-inj f → injective f
  strongly-inj→inj f ap#-f fx≡fy = A.tight λ x#y → B.irrefl' fx≡fy (ap#-f x#y)
```
