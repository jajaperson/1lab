<!--
```agda
open import 1Lab.Prelude hiding (_*_ ; _+_ ; _-_)

open import Algebra.Ring.Instances.Localisation
open import Algebra.Ring.Cancellative
open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring.Field
open import Algebra.Ring

open import Data.Set.Coequaliser hiding (_/_)
open import Data.Set.Apartness
open import Data.Sum.Base

open import Homotopy.Join

import Algebra.Ring.Instances.Localisation.Element as Le
import Algebra.Ring.Commutative.Element as Re
```
-->

```agda
module Algebra.Ring.Instances.Fractions {ℓ} (R : CRing ℓ) where
```

# Ring of fractions

Let $R$ be a [[commutative ring]] and $S$ be its set of `cancellable`{.Agda ident="is-cancellable"}
elements. Since $1 \in S$ and $S$ is closed under multiplication, we may
consider the localisation $\rm{Q}(R) := R[S\inv]$, called the **ring of
fractions** of $R$.

<--
```agda 
private
  module R where
    open CRing R public
    open Re R public

CancellableΩ : ⌞ R ⌟ → Ω
CancellableΩ x = elΩ (R.is-cancellable x)

private
  1ᶜΩ : □ (R.is-cancellable R.1r)
  1ᶜΩ = inc R.1-cancellable

  *ᶜΩ : ∀ {x y} → □ (R.is-cancellable x) → □ (R.is-cancellable y)
      → □ (R.is-cancellable (x R.* y))
  *ᶜΩ □xᶜ □yᶜ = inc (R.*-cancellable (□-out! □xᶜ) (□-out! □yᶜ))

CancellableΩ-multiplicative : Frac.is-multiplicative R (_∈ CancellableΩ)
CancellableΩ-multiplicative = record
  { has-1 = 1ᶜΩ
  ; has-* = *ᶜΩ
  }
```
-->

```agda
open Loc R CancellableΩ CancellableΩ-multiplicative renaming (S⁻¹R to Q) public
```

<!--
```agda
private module Q where
  open CRing Q using (ring) public
  open Re Q public

open Le CancellableΩ CancellableΩ-multiplicative

open CRing R

private instance
  H-Level-inv∗inv : ∀ {a b} {k} → H-Level ((Q.is-invertible a) ∗ (Q.is-invertible b)) (suc k)
  H-Level-inv∗inv = prop-instance (join-is-prop Q.is-invertible-is-prop Q.is-invertible-is-prop)
```
-->

The homomorphism $-/1 : R \to \rm{Q}(R)$ is then injective, and can
hence be regarded as an inclusion.

```agda
/1-injective : injective _/1
/1-injective {x} {y} x/1≡y/1 = case (Fr.effective x/1≡y/1) of
  λ u u-monic _ p → u-monic x y ((sym R.*-idr) ∙∙ p ∙∙ R.*-idr)
```

## When $R$ is an approximate integral domain

If $R$ is an [[approximate integral domain]] then $Q(R)$ is a
[[local ring]]. This is because if $x/s + y/t = 1$, then there exists a
$u \in C$ such that $uxt + uys = ust$. Since $ust$ is cancellable,
either $uxt$ or $uys$ is cancellable. In the first case, $sut/uxt$ is an
inverse for $x/s$, and in the second $tus/uys$ is an inverse for $y/t$.

```agda
module _ (ᵃcancellative : is-approx-integral-domain R) where
```

<!--
```agda
  private module Rᶜ = is-approx-cancellative ᵃcancellative

  open is-local
```
-->

```agda
  Q-is-local : is-local Q.ring
  Q-is-local .0≠1 0≡1 = Rᶜ.0≠1 (/1-injective 0≡1)
  Q-is-local .locality p = go _ _ p where
    go : ∀ a b → a +ₗ b ≡ 1ₗ → (Q.is-invertible a) ∗ (Q.is-invertible b)
    go = elim! λ x s sᵐ sᵉ y t tᵐ tᵉ p → case (Fr.effective p) of λ u uᵐ uᵉ p →
      let
        p : u * s * t ≡ u * x * t + u * y * s
        p =
          u * s * t                ≡⟨ cring! R ⟩
          u * 1r * (s * t)         ≡˘⟨ p ⟩
          u * (x * t + y * s) * 1r ≡⟨ cring! R ⟩
          u * x * t + u * y * s    ∎
          
        uxtᶜ∗uysᶜ : R.is-cancellable (u R.* x R.* t) ∗ R.is-cancellable (u R.* y R.* s)
        uxtᶜ∗uysᶜ = Rᶜ.cancellable-+ᶜ $ subst R.is-cancellable p
          (R.*-cancellable (R.*-cancellable (uᵐ , uᵉ) (sᵐ , sᵉ)) (tᵐ , tᵉ))

        q : ∀ {x s u t} → 1r * (x * (s * u * t)) * 1r ≡ 1r * 1r * (s * (u * x * t))
        q = cring! R
      in join-map
        (λ uxtᶜ → Q.has-section→invertible $ Q.make-section
          (inc ((s * u * t) / (u * x * t) [ inc uxtᶜ ]))
          (quot (Frac.inc 1r 1ᶜΩ q)))
        (λ uysᶜ → Q.has-section→invertible $ Q.make-section
          (inc ((t * u * s) / (u * y * s) [ inc uysᶜ ]))
          (quot (Frac.inc 1r 1ᶜΩ q)))
        uxtᶜ∗uysᶜ
```

## When $R$ is an integral domain

Moreover, if $R$ is an [[integral domain]] then $Q$ is a [[field]],
since any non-invertible element must have null numerator. 

```agda
module _ (idom : is-integral-domain R) where
```

<!--
```agda
  private module Rᶜ = is-cancellative idom

  open is-skewfield
```
-->

```agda
  Q-is-field : is-field Q
  Q-is-field .has-is-local = Q-is-local Rᶜ.has-is-approx
  Q-is-field .¬invertible→0 = case _ return (λ x → ¬(Q.is-invertible x) → x ≡ 0ₗ) of
    λ x s sᵐ sᵉ ¬inv →
      let
        f = x / s [ inc (sᵐ , sᵉ ) ]
        
        x≡0 : x ≡ 0r
        x≡0 = Rᶜ.¬cancellable→0 λ xᶜ →
          ¬inv (/-invertible f (/1-invertible x (inc xᶜ)))
      in num≡0 f x≡0
```

In this case, `_/1`{.Agda} is a [[strongly extensional function]] and
[[strong injection]] with respect to the canonical apartness relations
on $R$ and $\rm{Q}(R)$, as

```
  /1-strong-ext : is-strongly-ext Rᶜ.tight-apartness (tight-apartness Q-is-field) _/1
  /1-strong-ext {x} {y} x-y-inv = R.monic→cancellable λ a b p →
    let
      p/1 : inc (((x - y) * a) / 1r [ 1ᶜΩ ]) ≡ inc (((x - y) * b) / 1r [ 1ᶜΩ ])
      p/1 = ap _/1 p

      [x-y]⁻¹ = x-y-inv .Q.is-invertible.inv
    in /1-injective $
      a /1                                      ≡˘⟨ *ₗ-idl (a /1) ⟩
      ⌜ 1ₗ ⌝ *ₗ a /1                            ≡˘⟨ ap¡ (x-y-inv .Q.is-invertible.invr) ⟩
      ([x-y]⁻¹ *ₗ ⌜ x /1 +ₗ (- y) /1 ⌝) *ₗ a /1 ≡˘⟨ ap¡ (/1-hom .is-ring-hom.pres-+ _ _) ⟩
      ([x-y]⁻¹ *ₗ (x - y) /1) *ₗ a /1           ≡˘⟨ *ₗ-assoc [x-y]⁻¹ (x - y /1) (a /1) ⟩
      [x-y]⁻¹ *ₗ ⌜ (x - y) /1 *ₗ a /1 ⌝         ≡˘⟨ ap¡ (/1-hom .is-ring-hom.pres-* _ _) ⟩
      [x-y]⁻¹ *ₗ ((x - y) * a) /1               ≡⟨ ap ([x-y]⁻¹ *ₗ_) p/1 ⟩
      [x-y]⁻¹ *ₗ ⌜ ((x - y) * b) /1 ⌝           ≡⟨ ap! (/1-hom .is-ring-hom.pres-* _ _) ⟩
      [x-y]⁻¹ *ₗ ((x - y) /1 *ₗ b /1)           ≡⟨ *ₗ-assoc [x-y]⁻¹ (x - y /1) (b /1) ⟩
      [x-y]⁻¹ *ₗ ⌜ (x - y) /1 ⌝ *ₗ b /1         ≡⟨ ap! (/1-hom .is-ring-hom.pres-+ _ _) ⟩
      ⌜ [x-y]⁻¹ *ₗ (x /1 +ₗ (- y) /1) ⌝ *ₗ b /1 ≡⟨ ap! (x-y-inv .Q.is-invertible.invr) ⟩
      1ₗ *ₗ b /1                                ≡⟨ *ₗ-idl (b /1) ⟩
      b /1                                      ∎

  /1-strong-inj : is-strongly-inj Rᶜ.tight-apartness (tight-apartness Q-is-field) _/1
  /1-strong-inj {x} {y} x-yᶜ = let
      1/x-y : ⌞ Q ⌟
      1/x-y = (inc (1r / x - y [ inc x-yᶜ ]))
    in Q.has-retract→invertible $ Q.make-retract 1/x-y $
      1/x-y *ₗ ⌜ (x /1) -ₗ (y /1) ⌝ ≡˘⟨ ap¡ (/1-hom .is-ring-hom.pres-+ x (- y)) ⟩
      1/x-y *ₗ (x - y) /1 ≡⟨ /1-inverts (x - y) (inc x-yᶜ) ⟩
      1ₗ ∎
```

## When $R$ is a discrete integral domain

If $R$ is a [[discrete integral domain]], then $\rm{Q}(R)$ is a
[[discrete field]].

```agda
module _ (didom : is-discrete-integral-domain R) where
```

<!--
```agda
  private
    module Rᶜ = is-discrete-cancellative didom
    instance
      H-Level-invertible? : ∀ {x} {k} → H-Level (Q.is-invertible x ⊎ x ≡ 0ₗ) (suc k)
      H-Level-invertible? {x} = prop-instance (0≠1→invertible?-is-prop Q.ring (λ 0≡1 → Rᶜ.0≠1 (/1-injective 0≡1)) x)
```
-->

```agda
  open is-discrete-skewfield

  Q-is-discrete-field : is-discrete-field Q
  Q-is-discrete-field .0≠1 0≡1 = Rᶜ.0≠1 (/1-injective 0≡1)
  Q-is-discrete-field .invertible? = elim! λ x s sᵐ sᵉ →
    let
      x/s = x / s [ inc (sᵐ , sᵉ) ]
    in ⊎-map
      (λ xᶜ → /-invertible x/s (/1-invertible x (inc xᶜ)))
      (λ x≡0 → num≡0 x/s x≡0)
      (Rᶜ.cancellable? x)
```
