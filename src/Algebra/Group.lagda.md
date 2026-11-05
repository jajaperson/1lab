<!--
```agda
{-# OPTIONS -vtactic.hlevel:10 #-}
open import Algebra.Magma.Unital hiding (idl ; idr)
open import Algebra.Semigroup
open import Algebra.Monoid
open import Algebra.Magma

open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Properties
open import Cat.Prelude

import Algebra.Monoid.Reasoning as Mon

import Cat.Reasoning as Cat

open is-monoid hiding (idl ; idr)
```
-->

```agda
module Algebra.Group where
```

<!--
```agda
private variable
  ℓ : Level
```
-->

# Groups {defines=group}

A **group** is a [monoid] that has inverses for every element. The
inverse for an element is, [necessarily, unique]; thus, to say that "$(G,
\star)$ is a group" is a statement about $(G, \star)$ having a certain
_property_ (namely, being a group), not _structure_ on $(G, \star)$.

Furthermore, since [[group homomorphisms]]
automatically preserve this structure, we are justified in calling this
_property_ rather than _property-like structure_.

[monoid]: Algebra.Monoid.html
[necessarily, unique]: Algebra.Monoid.html#inverses

In particular, for a binary operator to be a group operator, it has to
`be a monoid`{.Agda ident=has-is-monoid}, meaning it must have a
`unit`{.Agda}.

```agda
record is-group {ℓ} {A : Type ℓ} (_*_ : A → A → A) : Type ℓ where
  no-eta-equality
  field
    unit : A
```

There is also a map which assigns to each element $x$ its _`inverse`{.Agda
ident=inverse}_ $x\inv$, and this inverse must multiply with $x$ to
give the unit, both on the left and on the right:

```agda
    inverse : A → A

    has-is-monoid : is-monoid unit _*_
    inversel : {x : A} → inverse x * x ≡ unit
    inverser : {x : A} → x * inverse x ≡ unit

  open is-monoid has-is-monoid public
```

<!--
```agda
  infixr 20 _—_
  _—_ : A → A → A
  x — y = x * inverse y

  abstract
    inv-unit : inverse unit ≡ unit
    inv-unit = monoid-inverse-unique
      has-is-monoid unit _ _ inversel (has-is-monoid .is-monoid.idl)

    inv-inv : ∀ {x} → inverse (inverse x) ≡ x
    inv-inv = monoid-inverse-unique
      has-is-monoid _ _ _ inversel inversel

    inv-comm : ∀ {x y} → inverse (x * y) ≡ inverse y — x
    inv-comm {x = x} {y} =
      monoid-inverse-unique has-is-monoid _ _ _ inversel p
      where
        p : (x * y) * (inverse y — x) ≡ unit
        p = associative has-is-monoid
         ∙∙ ap₂ _*_
              (  sym (associative has-is-monoid)
              ∙∙ ap₂ _*_ refl inverser
              ∙∙ has-is-monoid .is-monoid.idr)
              refl
         ∙∙ inverser

    zero-diff : ∀ {x y} → x — y ≡ unit → x ≡ y
    zero-diff {x = x} {y = y} p =
      monoid-inverse-unique has-is-monoid _ _ _ p inversel

  underlying-monoid : Monoid ℓ
  underlying-monoid = el! A , record
    { identity = unit ; _⋆_ = _*_ ; has-is-monoid = has-is-monoid }

  open Mon underlying-monoid public
  
  inv-is-equiv : is-equiv inverse
  inv-is-equiv = is-iso→is-equiv $ iso inverse (λ x → inv-inv) λ x → inv-inv
```
-->

Note that any element $x$ of $G$ determines two
bijections on the underlying set of $G$, by multiplication with $x$ on
the left and on the right.
The inverse of this bijection is given by multiplication with
$x\inv$, and the proof that these are in fact inverse functions are
given by the group laws:

```agda
  ⋆-equivl : ∀ x → is-equiv (x *_)
  ⋆-equivl x = is-iso→is-equiv (iso (inverse x *_)
    (λ _ → cancell inverser) λ _ → cancell inversel)

  ⋆-equivr : ∀ y → is-equiv (_* y)
  ⋆-equivr y = is-iso→is-equiv (iso (_* inverse y)
    (λ _ → cancelr inversel) λ _ → cancelr inverser)
```

## is-group is propositional

Showing that `is-group`{.Agda} takes values in propositions is
straightforward, but, fortunately, very easy to automate: Our automation
takes care of all the propositional components, and we've already
established that units and inverses (thus inverse-assigning maps) are
unique in a monoid.

```agda
private unquoteDecl eqv = declare-record-iso eqv (quote is-group)

is-group-is-prop : ∀ {ℓ} {A : Type ℓ} {_*_ : A → A → A}
                 → is-prop (is-group _*_)
is-group-is-prop {A = A} x y = Iso.injective eqv $
     1x=1y
  ,ₚ funext (λ a →
      monoid-inverse-unique x.has-is-monoid a _ _
        x.inversel
        (y.inverser ∙ sym 1x=1y))
  ,ₚ prop!
  where
    module x = is-group x
    module y = is-group y hiding (magma-hlevel)
    A-hl : ∀ {n} → H-Level A (2 + n)
    A-hl = basic-instance {T = A} 2 (x .is-group.has-is-set)
    1x=1y = identities-equal _ _
      (is-monoid→is-unital-magma x.has-is-monoid)
      (is-monoid→is-unital-magma y.has-is-monoid)

instance
  H-Level-is-group
    : ∀ {ℓ} {G : Type ℓ} {_+_ : G → G → G} {n}
    → H-Level (is-group _+_) (suc n)
  H-Level-is-group = prop-instance is-group-is-prop
```

# Group homomorphisms {defines="group-homomorphism"}

In contrast with monoid homomorphisms, for group homomorphisms, it is
not necessary for the underlying map to explicitly preserve the unit
(and the inverses); It is sufficient for the map to preserve the
multiplication.

As a stepping stone, we define what it means to equip a type with a
group structure: a `group structure on`{.Agda ident=Group-on} a type.

```agda
record Group-on {ℓ} (A : Type ℓ) : Type ℓ where
  field
    _⋆_ : A → A → A
    has-is-group : is-group _⋆_

  infixr 20 _⋆_
  infixl 35 _⁻¹

  _⁻¹ : A → A
  x ⁻¹ = has-is-group .is-group.inverse x

  open is-group has-is-group public
```

We have that a map `is a group homomorphism`{.Agda ident=is-group-hom} if
it `preserves the multiplication`{.Agda ident=pres-⋆}.

```agda
record
  is-group-hom
    {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    (G : Group-on A) (G' : Group-on B) (e : A → B) : Type (ℓ ⊔ ℓ') where
  private
    module A = Group-on G
    module B = Group-on G'

  field
    pres-⋆ : (x y : A) → e (x A.⋆ y) ≡ e x B.⋆ e y
```

A tedious calculation shows that this is sufficient to preserve the
identity and inverses:

```agda
  private
    1A = A.unit
    1B = B.unit

  pres-id : e 1A ≡ 1B
  pres-id =
    e 1A                       ≡⟨ sym B.idr ⟩
    e 1A B.⋆ ⌜ 1B ⌝            ≡˘⟨ ap¡ B.inverser ⟩
    e 1A B.⋆ (e 1A B.— e 1A)   ≡⟨ B.associative ⟩
    ⌜ e 1A B.⋆ e 1A ⌝ B.— e 1A ≡⟨ ap! (sym (pres-⋆ _ _) ∙ ap e A.idl) ⟩
    e 1A B.— e 1A              ≡⟨ B.inverser ⟩
    1B                         ∎

  pres-inv : ∀ {x} → e (A.inverse x) ≡ B.inverse (e x)
  pres-inv {x} =
    monoid-inverse-unique B.has-is-monoid (e x) _ _
      (sym (pres-⋆ _ _) ∙∙ ap e A.inversel ∙∙ pres-id)
      B.inverser

  pres-diff : ∀ {x y} → e (x A.— y) ≡ e x B.— e y
  pres-diff {x} {y} =
    e (x A.— y)                 ≡⟨ pres-⋆ _ _ ⟩
    e x B.⋆ ⌜ e (A.inverse y) ⌝ ≡⟨ ap! pres-inv ⟩
    e x B.— e y                 ∎
```

<!--
```agda
is-group-hom-is-prop
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
      {G : Group-on A} {H : Group-on B} {f}
  → is-prop (is-group-hom G H f)
is-group-hom-is-prop {H = H} a b i .is-group-hom.pres-⋆ x y =
  Group-on.has-is-set H _ _ (a .is-group-hom.pres-⋆ x y) (b .is-group-hom.pres-⋆ x y) i

instance
  H-Level-group-hom
    : ∀ {n} {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
      {G : Group-on A} {H : Group-on B} {f}
    → H-Level (is-group-hom G H f) (suc n)
  H-Level-group-hom = prop-instance is-group-hom-is-prop

module _ where
  open is-group-hom
  open Group-on
```
-->

:::{.definition #category-of-groups}

It follows that groups and their homomorphisms form a category.

```agda
  Group-structure : ∀ ℓ → Thin-structure ℓ Group-on
  Group-structure ℓ .is-hom f G G' = el! (is-group-hom G G' f)
  Group-structure ℓ .id-is-hom        .pres-⋆ x y = refl
  Group-structure ℓ .∘-is-hom f g α β .pres-⋆ x y =
    ap f (β .pres-⋆ x y) ∙ α .pres-⋆ _ _
  Group-structure ℓ .id-hom-unique {s = s} {t = t} α β i =
    record
      { _⋆_          = λ x y → α .pres-⋆ x y i
      ; has-is-group =
        is-prop→pathp (λ i → is-group-is-prop {_*_ = λ x y → α .pres-⋆ x y i})
          (s .has-is-group)
          (t .has-is-group)
          i
      }
  Groups : ∀ ℓ → Precategory (lsuc ℓ) ℓ
  Groups ℓ = Structured-objects (Group-structure ℓ)
  module Groups {ℓ} = Cat (Groups ℓ)

  Groups-is-category : ∀ {ℓ} → is-category (Groups ℓ)
  Groups-is-category = Structured-objects-is-category (Group-structure _)

  instance
    Groups-equational : ∀ {ℓ} → is-equational (Group-structure ℓ)
    Groups-equational .is-equational.invert-id-hom x .pres-⋆ a b = sym (x .pres-⋆ a b)

  Group : ∀ ℓ → Type (lsuc ℓ)
  Group _ = Groups.Ob
```

:::

The category of groups admits a `faithful`{.Agda ident=is-faithful}
functor into the category of sets, written $U : \rm{Groups} \to
\Sets$, which projects out the underlying set of the group. Faithfulness
of this functor says, in more specific words, that equality of group
homomorphisms can be tested by comparing the underlying morphisms of
sets.

```agda
Grp↪Sets : Functor (Groups ℓ) (Sets ℓ)
Grp↪Sets = Forget-structure (Group-structure _)

Grp↪Sets-is-faithful : is-faithful (Grp↪Sets {ℓ})
Grp↪Sets-is-faithful = Structured-hom-path (Group-structure _)
```

# Making groups

Since the interface of `Group-on`{.Agda} is very deeply nested, we
introduce a helper function for arranging the data of a group into a
record.

```agda
record make-group {ℓ} (G : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    group-is-set : is-set G
    unit : G
    mul  : G → G → G
    inv  : G → G

    assoc : ∀ x y z → mul x (mul y z) ≡ mul (mul x y) z
    invl  : ∀ x → mul (inv x) x ≡ unit
    idl   : ∀ x → mul unit x ≡ x

  private
    invr : ∀ x → mul x (inv x) ≡ unit
    invr x =
      mul x (inv x)                                   ≡˘⟨ idl _ ⟩
      mul unit (mul x (inv x))                        ≡˘⟨ ap₂ mul (invl _) refl ⟩
      mul (mul (inv (inv x)) (inv x)) (mul x (inv x)) ≡˘⟨ assoc _ _ _ ⟩
      mul (inv (inv x)) (mul (inv x) (mul x (inv x))) ≡⟨ ap₂ mul refl (assoc _ _ _) ⟩
      mul (inv (inv x)) (mul (mul (inv x) x) (inv x)) ≡⟨ ap₂ mul refl (ap₂ mul (invl _) refl) ⟩
      mul (inv (inv x)) (mul unit (inv x))            ≡⟨ ap₂ mul refl (idl _) ⟩
      mul (inv (inv x)) (inv x)                       ≡⟨ invl _ ⟩
      unit                                            ∎

  to-is-group : is-group mul
  to-is-group .is-group.unit = unit
  to-is-group .is-group.inverse = inv
  to-is-group .is-group.inversel = invl _
  to-is-group .is-group.inverser = invr _
  to-is-group .is-group.has-is-monoid .is-monoid.idl {x} = idl x
  to-is-group .is-group.has-is-monoid .is-monoid.idr {x} =
    mul x ⌜ unit ⌝           ≡˘⟨ ap¡ (invl x) ⟩
    mul x (mul (inv x) x)    ≡⟨ assoc _ _ _ ⟩
    mul ⌜ mul x (inv x) ⌝ x  ≡⟨ ap! (invr x) ⟩
    mul unit x               ≡⟨ idl x ⟩
    x                        ∎
  to-is-group .is-group.has-is-monoid .has-is-semigroup =
    record { has-is-magma = record { has-is-set = group-is-set }
           ; associative = λ {x y z} → assoc x y z
           }

  to-group-on : Group-on G
  to-group-on .Group-on._⋆_ = mul
  to-group-on .Group-on.has-is-group = to-is-group

  to-group : Group ℓ
  to-group = (el G group-is-set) , to-group-on

open make-group using (to-is-group; to-group-on ; to-group) public
```

<!--
```agda
open Group-on
open is-group-hom

Lift-group : ∀ {ℓ} ℓ' → Group ℓ → Group (ℓ ⊔ ℓ')
Lift-group {ℓ} ℓ' G = G' where
  module G = Group-on (G .snd)
  open is-group
  open is-monoid
  open is-semigroup
  open is-magma

  G' : Group (ℓ ⊔ ℓ')
  G' .fst = el! (Lift ℓ' ⌞ G ⌟)
  G' .snd ._⋆_ (lift x) (lift y) = lift (x G.⋆ y)
  G' .snd .has-is-group .unit = lift G.unit
  G' .snd .has-is-group .inverse (lift x) = lift (G.inverse x)
  G' .snd .has-is-group .has-is-monoid .has-is-semigroup .has-is-magma .has-is-set = hlevel 2
  G' .snd .has-is-group .has-is-monoid .has-is-semigroup .associative = ap lift G.associative
  G' .snd .has-is-group .has-is-monoid .idl = ap lift G.idl
  G' .snd .has-is-group .has-is-monoid .idr = ap lift G.idr
  G' .snd .has-is-group .inversel = ap lift G.inversel
  G' .snd .has-is-group .inverser = ap lift G.inverser

G→LiftG : ∀ {ℓ} (G : Group ℓ) → Groups.Hom G (Lift-group lzero G)
G→LiftG G .fst = lift
G→LiftG G .snd .pres-⋆ _ _ = refl
```
-->
