<!--
```agda
open import Algebra.Group.Subgroup hiding (incl)
open import Algebra.Ring.Ideal
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude hiding (_*_ ; _+_ ; _-_)

open import Data.Power
open import Data.Dec

import Algebra.Ring.Reasoning as Kit
```
-->

```agda
module Algebra.Ring.Instances.Quotient {ℓ} (R : Ring ℓ) where
```

<!--
```agda
open Ring-on (R .snd)
private module R = Kit R
```
-->

# Quotient rings {defines="quotient-ring"}

Let $R$ be a [[ring]] and $I \sube R$ be an ideal. Because rings have an
underlying [[abelian group]], the ideal $I \sube R$ determines a normal
subgroup $I$ of $R$'s additive group, so that we may form the quotient
group $R/I$. And since ideals are closed under multiplication^[recall
that all our rings are commutative, so they're closed under
multiplication by a constant on either side], we can extend $R$'s
multiplication to a multiplication operation on $R/I$ in a canonical
way! In that case, we refer to $R/I$ as a **quotient ring**.

[quotient group]: Algebra.Group.Subgroup.html#representing-kernels

<!--
```agda
module _ {I : ℙ ⌞ R ⌟} (idl : is-ideal R I) where
  private module I where
    open is-ideal idl public
    open Congruence (normal-subgroup→congruence R.additive-group ideal→normal) public
```
-->

Really, the bulk of the construction has already been done (in the
section about quotient groups), so all that remains is the following
construction: We want to show that $xy$ is invariant under equivalence
for both $x$ and $y$ (and we may treat them separately for
comprehensibility's sake).

<!--
```agda
  private
    quot-grp : Group _
    quot-grp = R.additive-group /ᴳ I.ideal→normal
    module R/I = Group-on (quot-grp .snd) hiding (magma-hlevel)
```
-->

```agda
    quot-mul : ⌞ quot-grp ⌟ → ⌞ quot-grp ⌟ → ⌞ quot-grp ⌟
    quot-mul =
      Coeq-rec₂ squash (λ x y → inc (x R.* y))
        (λ a (_ , _ , r) → p1 a r)
        (λ a (_ , _ , r) → p2 a r)
        where
```

On one side, we must show that $[ax] = [ay]$ supposing that $[x] = [y]$,
i.e. that $(x - y) \in I$. But since $I$ is an ideal, we have $(ax - ay)
\in I$, thus $[ax] = [ay]$. And on the other side, we have the same
thing: Since $(x - y) \in I$, also $(xa - ya) \in I$, so $[xa] = [ya]$.

```agda
      p1 : ∀ a {x y} (r : (x R.- y) ∈ I) → inc (x R.* a) ≡ inc (y R.* a)
      p1 a {x} {y} x-y∈I = quot $ subst (_∈ I)
        (R.*-distribr ∙ ap (x R.* a R.+_) R.*-negatel)
        (I.has-*ᵣ a x-y∈I)

      p2 : ∀ a {x y} (r : (x R.- y) ∈ I) → inc (a R.* x) ≡ inc (a R.* y)
      p2 a {x} {y} x-y∈I = quot $ subst (_∈ I)
        (R.*-distribl ∙ ap (a R.* x R.+_) R.*-negater)
        (I.has-*ₗ a x-y∈I)
```

<details>
<summary>Showing that this extends to a ring structure on $R/I$ is annoying, but
not non-trivial, so we keep in this `<details>`{.Agda} fold. Most of the proof is appealing to the elimination principle(s) for
quotients into propositions, then applying $R$'s laws.</summary>

```agda
  make-R/I : make-ring ⌞ quot-grp ⌟
  make-R/I = let open make-ring in λ where
    .ring-is-set → squash
    .0R → inc 0r
    ._+_ → R/I._⋆_
    .-_ → R/I.inverse
    .+-idl x → R/I.idl
    .+-invr x → R/I.inverser {x}
    .+-assoc x y z → R/I.associative {x} {y} {z}
    .1R → inc R.1r
    ._*_ → quot-mul
    .+-comm → elim! λ x y → ap Coeq.inc R.+-commutes
    .*-idl → elim! λ x → ap Coeq.inc R.*-idl
    .*-idr → elim! λ x → ap Coeq.inc R.*-idr
    .*-assoc → elim! λ x y z → ap Coeq.inc R.*-associative
    .*-distribl → elim! λ x y z → ap Coeq.inc R.*-distribl
    .*-distribr → elim! λ x y z → ap Coeq.inc R.*-distribr
```

</details>

```agda
  R/I : Ring ℓ
  R/I = to-ring make-R/I
```

As a quick aside, if $I$ is a complemented ideal (equivalently: a
decidable ideal), and $R$ is a discrete ring, then the quotient ring is
also discrete. This is a specialisation of a general result about
decidable quotient sets, but we mention it here regardless:

```agda
  Discrete-ring-quotient : (∀ x → Dec (x ∈ I)) → Discrete ⌞ R/I ⌟
  Discrete-ring-quotient dec∈I = Discrete-quotient
    (normal-subgroup→congruence R.additive-group I.ideal→normal)
    (λ x y → dec∈I (x R.- y))
```

The natural projection `inc`{.Agda} defines a ring homomorphism
$\mathrm{incl} R \to R/I$.

<!--
```agda
  open is-ring-hom
```
-->

```agda
  incl : Rings.Hom R R/I
  incl .fst = inc
  incl .snd .pres-+ _ _ = refl
  incl .snd .pres-id = refl
  incl .snd .pres-* _ _ = refl
```

:::{.definition #ideals-are-kernels}

The [[kernel|ring kernel]] of `incl`{.Agda} is... the ideal $I$! As a
corollary, ideals of rings are precisely kernels of ring homomorphisms.

```agda
  𝔨𝔢𝔯[incl]≡I : 𝔨𝔢𝔯 incl ≡ I
  𝔨𝔢𝔯[incl]≡I = funext λ x → Ω-ua
    (elim! λ fx≡0 → subst (_∈ I)
      (ap (x R.+_) R.a.inv-unit ∙ R.+-idr)
      (I.effective fx≡0))
    (elim! λ x∈I → inc (quot $ subst (_∈ I)
      (sym (ap (x R.+_) R.a.inv-unit ∙ R.+-idr))
      x∈I))
```

:::

## Universal property

One can adopt the alternate point of view that the quotient ring _with
respect to a predicate_ $I : \bb P(R)$ is a ring homomorphism $\pi : R
\to R/I$ satisfying a universal property. Namely, $\pi$ annihilates $I$,

<!--
```agda
module _ (I : ℙ ⌞ R ⌟) where
```
-->

```agda
  I→0 : ∀ {S} (f : Rings.Hom R S) → Type ℓ
  I→0 {S} f = let module S = Ring-on (S .snd) in ∀ {x} → x ∈ I → f · x ≡ S.0r
```

and if $f : R \to S$ is a ring homomorphism annihilating $I$, then there
exists a unique homomorphism $\bar{f} : R/I \to S$ factoring $f$.

~~~{.quiver}
\[\begin{tikzcd}
  R && S \\
  \\
  {R/I}
  \arrow["f", from=1-1, to=1-3]
  \arrow["{\rm{incl}}"', two heads, from=1-1, to=3-1]
  \arrow["{\bar{f}}"', dashed, from=3-1, to=1-3]
\end{tikzcd}\]
~~~

```agda
  record is-quotient-ring {Q} (π : Rings.Hom R Q) : Type (lsuc ℓ) where
    private module Q = Ring-on (Q .snd)
    field
      πI→0 : I→0 π
      universal : ∀ {S} (f : Rings.Hom R S) → I→0 f → Rings.Hom Q S
      factors
        : ∀ {S} {f : Rings.Hom R S} {fI→0 : I→0 f}
        → universal f fI→0 Rings.∘ π ≡ f
      unique
        : ∀ {S} {f : Rings.Hom R S} {fI→0 : I→0 f} {h : Rings.Hom Q S}
        → h Rings.∘ π ≡ f → universal f fI→0 ≡ h

    unique₂
      : ∀ {S} {f : Rings.Hom R S} {fI→0 : I→0 f} {h h' : Rings.Hom Q S}
      → h Rings.∘ π ≡ f → h' Rings.∘ π ≡ f
      → h ≡ h'
    unique₂ {S} {f} {fI→0} p q = sym (unique {fI→0 = fI→0} p) ∙ (unique q)
```

It then follows that any two quotient rings for the same $R$ and $I$ are
isomorphic.

```agda
  quotient-ring-unique : ∀ {Q π} (Q𐞥 : is-quotient-ring {Q} π) {Q' π'} (Q'𐞥 : is-quotient-ring {Q'} π') → Q Rings.≅ Q'
  quotient-ring-unique {Q} {π} Q𐞥 {Q'} {π'} Q'𐞥 = Rings.make-iso Q→Q' Q'→Q Q'→Q→Q' Q→Q'→Q where
    module Q = is-quotient-ring Q𐞥
    module Q' = is-quotient-ring Q'𐞥
    Q→Q' : Rings.Hom Q Q'
    Q→Q' = Q.universal π' Q'.πI→0

    Q'→Q : Rings.Hom Q' Q
    Q'→Q = Q'.universal π Q.πI→0

    Q→Q'→Q : Q'→Q Rings.∘ Q→Q' ≡ Rings.id
    Q→Q'→Q = Q.unique₂ {fI→0 = Q.πI→0}
      (
        (Q'→Q Rings.∘ Q→Q') Rings.∘ π   ≡˘⟨ Rings.assoc Q'→Q Q→Q' π ⟩
        Q'→Q Rings.∘ ⌜ Q→Q' Rings.∘ π ⌝ ≡⟨ ap! Q.factors ⟩
        Q'→Q Rings.∘ π'                 ≡⟨ Q'.factors ⟩
        π                               ∎
      ) (Rings.idl π)

    Q'→Q→Q' : Q→Q' Rings.∘ Q'→Q ≡ Rings.id
    Q'→Q→Q' = Q'.unique₂ {fI→0 = Q'.πI→0}
      (
        (Q→Q' Rings.∘ Q'→Q) Rings.∘ π'   ≡˘⟨ Rings.assoc Q→Q' Q'→Q π' ⟩
        Q→Q' Rings.∘ ⌜ Q'→Q Rings.∘ π' ⌝ ≡⟨ ap! Q'.factors ⟩
        Q→Q' Rings.∘ π                   ≡⟨ Q.factors ⟩
        π'                               ∎
      ) (Rings.idl π')
```

The construction of `R/I`{.Agda} above shows that the quotient ring
always exists, provided $I$ is an ideal.

<!--
```agda
module _ {I : ℙ ⌞ R ⌟} (idl : is-ideal R I) where
```
-->

```agda
  R/I-is-quotient : is-quotient-ring I (incl idl)
  R/I-is-quotient = let open is-quotient-ring in λ where
    .πI→0 {x} → elim! λ x∈I → quot $ subst (_∈ I)
      (sym (ap (x R.+_) R.a.inv-unit ∙ R.+-idr)) x∈I
    .universal {S} f fI→0 →
      let module S = Ring-on (S .snd)
          module f = is-ring-hom (f .snd)
      in λ where
        .fst → Quot-elim (λ _ → hlevel 2) (f .fst) λ x y x-y∈I → S.zero-diff $
          f · x S.+ ⌜ S.- f · y ⌝ ≡˘⟨ ap¡ f.pres-neg ⟩
          f · x S.+ f · (- y)     ≡˘⟨ f.pres-+ x (R.- y) ⟩
          f · (x - y)             ≡⟨ fI→0 x-y∈I ⟩
          S.0r                    ∎
        .snd → let open is-ring-hom in λ where
          .pres-+ → elim! f.pres-+
          .pres-* → elim! f.pres-*
          .pres-id → f.pres-id
    .factors → Structured-hom-path (Ring-structure ℓ) refl
    .unique p → reext! (sym p)
```
