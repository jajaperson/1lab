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
  ℓ ℓ' : Level
  A : Type ℓ
```
-->

# Apartness relations {defines="apartness-relation"}

An **apartness relation** on a type $A$ is a (mere) relation $\apt$ on
$A$ satisfying properties that are in some sense complementary to a
[[congruence]]: it is _irreflexive_, _cotransitive_, and _symmetric_.

```agda
record Apartness (A : Type ℓ) ℓ' : Type (ℓ ⊔ lsuc ℓ') where
  field
    _#_ : A → A → Type ℓ'
    has-is-prop : ∀ {x y} → is-prop (x # y)
    irrefl : ∀ {x} → ¬(x # x)
    cotrans : ∀ {x y z} → x # z → (x # y) ∗ (y # z)
    symᵃ : ∀ {x y} → x # y → y # x

  irrefl' : ∀ {x y} → x ≡ y → ¬(x # y)
  irrefl' {x} x≡y = subst (λ y → ¬(x # y)) x≡y irrefl
```

<!--
```agda
Lift-apartness : ∀ ℓ' → Apartness A ℓ → Apartness A (ℓ ⊔ ℓ')
Lift-apartness ℓ' apt = record where
  open Apartness apt
  _#_ x y = Lift ℓ' (x # y)
  has-is-prop = Lift-is-hlevel 1 has-is-prop
  irrefl = irrefl ∘ lower
  cotrans = λ x → join-map lift lift $ cotrans $ lower x
  symᵃ = lift ∘ symᵃ ∘ lower

open hlevel-projection
private
  #-prop : ∀ (apt : Apartness A ℓ) {x y} → is-prop (apt .Apartness._#_ x y)
  #-prop = Apartness.has-is-prop

instance
  Apartness-#-hlevel-proj : hlevel-projection (quote Apartness._#_)
  Apartness-#-hlevel-proj .has-level = quote #-prop
  Apartness-#-hlevel-proj .get-level _ = pure (quoteTerm (suc zero))
  Apartness-#-hlevel-proj .get-argument = first-visible

private unquoteDecl apt-eqv = declare-record-iso apt-eqv (quote Apartness)
module _ {apt apt' : Apartness A ℓ} (p : ∀ x y → apt .Apartness._#_ x y ≃ apt' .Apartness._#_ x y) where
  private
    module apt = Apartness apt
    module apt' = Apartness apt'

  open Apartness

  private
    lemma : ∀ {x y} i → is-prop (ua (p x y) i)
    lemma {x} {y} i = is-prop→pathp (λ i → is-prop-is-prop {A = ua (p x y) i}) apt.has-is-prop apt'.has-is-prop i

  Apartness-path : apt ≡ apt'
  Apartness-path i ._#_ x y = ua (p x y) i
  Apartness-path i .has-is-prop = lemma i
  Apartness-path i .irrefl = is-prop→pathp (λ i → Π-is-hlevel {A = ua (p _ _) i} 1 λ _ ()) apt.irrefl apt'.irrefl i
  Apartness-path i .cotrans {x} {y} {z} = is-prop→pathp (λ i → Π-is-hlevel {A = ua (p x z) i} 1 λ _ → join-is-prop (lemma i) (lemma i)) apt.cotrans apt'.cotrans i
  Apartness-path i .symᵃ = is-prop→pathp (λ i → Π-is-hlevel {A = ua (p _ _) i} 1 λ _ → lemma i) apt.symᵃ apt'.symᵃ i
```
-->

The complement of an apartness relation on $A$ is a congruence on $A$.

```agda
Apartness→Congruence : Apartness A ℓ' → Congruence A ℓ'
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

```agda
record Aset-on (A : Type ℓ) ℓ' : Type (ℓ ⊔ lsuc ℓ') where
  field
    apartness : Apartness A ℓ'
```

<!--
```agda
  open Apartness apartness public

  field
```
-->

```agda
    tight : ∀ {x y} → ¬(x # y) → x ≡ y
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

Aset : ∀ ℓ ℓ' → Type (lsuc ℓ ⊔ lsuc ℓ')
Aset ℓ ℓ' = Σ (Type ℓ) λ A → Aset-on A ℓ'
```

<!--
```agda
Lift-aset-on :  ∀ ℓ' → Aset-on A ℓ → Aset-on A (ℓ ⊔ ℓ')
Lift-aset-on ℓ' Aᵃ = record where
  module Aᵃ = Aset-on Aᵃ
  apartness = Lift-apartness ℓ' Aᵃ.apartness
  tight = Aᵃ.tight ∘ (_∘ lift)
```
-->

## Stable tight apartness relations

Let $A$ be a [[discrete]] set. Then $A$ is an aset under denial
inequality.

<!--
```agda
module _ {A : Type ℓ} (disc : Discrete A) where
  instance Dec-Path-A = disc
```
-->

```agda
  discrete→aset : Aset-on A ℓ
  discrete→aset = record where
    apartness = record where
      _#_ = _≠_
      irrefl x≠x = x≠x refl
      symᵃ x≠y y≡x = x≠y (sym y≡x)
      cotrans {x} {y} {z} x≠z = caseᵈ (x ≡ y) of λ where
        (yes x≡y) → inr λ y≡z → x≠z (x≡y ∙ y≡z)
        (no x≠z) → inl x≠z
      has-is-prop = hlevel 1
    tight = dec→dne
```

More generally, any $\neg\neg$-stable tight apartness relation is
logically equivalent to denial inequality.

<!--
```agda
module _ (Aᵃ : Aset-on A ℓ') where
  open Aset-on Aᵃ
```
-->

```agda
  #-is-stable : Type (level-of A ⊔ ℓ')
  #-is-stable = ∀ {x y} → ¬ ¬(x # y) → x # y

  #-is-stable→#≃≠ : #-is-stable → ∀ {x y} → (x # y) ≃ (x ≠ y)
  #-is-stable→#≃≠ stable = prop-ext has-is-prop (hlevel 1)
    (λ x#y x≡y → irrefl' x≡y x#y)
    λ x≠y → stable (x≠y ∘ tight)
```
