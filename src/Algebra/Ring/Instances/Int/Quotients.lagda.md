<!--
```agda
{-# OPTIONS --no-qualified-instances #-}
open import Algebra.Ring.Instances.Quotient
open import Algebra.Ring.Instances.Lift
open import Algebra.Ring.Cat.Initial
open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Ring.Ideal
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude

open import Data.Fin.Arithmetic
open import Data.Int.Properties
open import Data.Nat.Properties
open import Data.Int.DivMod
open import Data.Nat.DivMod
open import Data.Fin.Base
open import Data.Int.Base hiding (Positive)
open import Data.Nat.Base
open import Data.Power

import Algebra.Ring.Reasoning as Rr

open Algebra.Ring.Cat.Initial
```
-->

```agda
module Algebra.Ring.Instances.Int.Quotients where
```

# Rings of integers modulo $n$

Given a positive $n : \NN$, the ring $\ZZ_m$ of integers modulo $n$ can
be concretely constructed as a ring structure on the [[standard finite
set]] $\operatorname{Fin}(n)$ via [[modular arithmetic]].

```agda
ℤ/⟨_⟩ : ∀ n ⦃ _ : Positive n ⦄ → Ring lzero
ℤ/⟨ n ⟩ = to-ring {R = Fin n} record
  { ring-is-set = hlevel 2
  ; 0R = 0
  ; _+_ = _+ₘ_
  ; -_ = -ₘ_
  ; +-idl = +ₘ-zerol
  ; +-invr = +ₘ-invr
  ; +-assoc = +ₘ-associative
  ; +-comm = +ₘ-commutative
  ; 1R = 1ₘ
  ; _*_ = _*ₘ_
  ; *-idl = *ₘ-onel
  ; *-idr = *ₘ-oner
  ; *-assoc = *ₘ-associative
  ; *-distribl = *ₘ-distrib-+ₘl
  ; *-distribr = *ₘ-distrib-+ₘr
  }
```

<!--
```agda
module _ {n} ⦃ _ : Positive n ⦄ where
  open Explicit ℤ-comm
```
-->

This ring comes equipped with a ring homomorphism $\pi : \ZZ \to \ZZ_n :
x \mapsto [x]$

```agda
  [_] : Int → Fin n
  [ x ] = fin (x %ℤ n) ⦃ x%ℤy<y x n ⦄

  π-hom  : is-ring-hom (ℤ .snd) (ℤ/⟨ n ⟩ .snd) [_]
```

<details>
<summary>
Showing $\pi$ is a homomorphism is straightfoward but cumbersome, so we
do it in this `<details>` tag.
</summary>

```agda
  π-hom = let open is-ring-hom in λ where
    .pres-id → refl
    .pres-+ x y → fin-ap $
      (x +ℤ y) %ℤ n                                                               ≡⟨ ap (_%ℤ n) $ ap₂ _+ℤ_ (is-divmodℤ x n) (is-divmodℤ y n) ⟩
      (x /ℤ n *ℤ pos n +ℤ pos (x %ℤ n) +ℤ (y /ℤ n *ℤ pos n +ℤ pos (y %ℤ n))) %ℤ n ≡⟨ ap (_%ℤ n) $ solve 5 (λ p q r s n → (((p :* n) :+ r) :+ ((q :* n) :+ s)) ≔ ((p :+ q) :* n :+ (r :+ s))) (x /ℤ n) (y /ℤ n) (pos (x %ℤ n)) (pos (y %ℤ n)) (pos n) refl ⟩
      ((x /ℤ n +ℤ y /ℤ n) *ℤ (pos n) +ℤ (pos (x %ℤ n) +ℤ pos (y %ℤ n))) %ℤ n      ≡⟨ %ℤ-clear n (x /ℤ n +ℤ y /ℤ n) (pos (x %ℤ n) +ℤ pos (y %ℤ n)) ⟩
      pos (x %ℤ n + y %ℤ n) %ℤ n                                                  ≡⟨⟩
      ((x %ℤ n) + (y %ℤ n)) % n                                                   ∎
    .pres-* x y → fin-ap $
      x *ℤ y %ℤ n                                                                 ≡⟨ ap (_%ℤ n) $ ap₂ _*ℤ_ (is-divmodℤ x n) (is-divmodℤ y n) ⟩
      (x /ℤ n *ℤ pos n +ℤ pos (x %ℤ n)) *ℤ (y /ℤ n *ℤ pos n +ℤ pos (y %ℤ n)) %ℤ n ≡⟨ ap (_%ℤ n) $ solve 5 (λ p q r s n → ((p :* n :+ r) :* ((q :* n) :+ s)) ≔ ((((p :* q :* n) :+ (p :* s) :+ (r :* q)) :* n) :+ r :* s)) (x /ℤ n) (y /ℤ n) (pos (x %ℤ n)) (pos (y %ℤ n)) (pos n) refl ⟩
      (
        (
          x /ℤ n *ℤ (y /ℤ n) *ℤ pos n +ℤ x /ℤ n *ℤ pos (y %ℤ n)
          +ℤ pos (x %ℤ n) *ℤ (y /ℤ n)
         ) *ℤ pos n
        +ℤ pos (x %ℤ n) *ℤ pos (y %ℤ n)
      ) %ℤ n                            ≡⟨ %ℤ-clear n ((x /ℤ n) *ℤ (y /ℤ n) *ℤ pos n +ℤ (x /ℤ n) *ℤ pos (y %ℤ n) +ℤ pos (x %ℤ n) *ℤ (y /ℤ n)) (pos (x %ℤ n) *ℤ pos (y %ℤ n)) ⟩
      pos (x %ℤ n) *ℤ pos (y %ℤ n) %ℤ n ≡⟨ ap (_%ℤ n) (assign-pos _) ⟩
      pos (x %ℤ n * (y %ℤ n)) %ℤ n      ≡⟨⟩
      (x %ℤ n * (y %ℤ n)) % n           ∎
```

</details>

```agda
  π : Rings.Hom ℤ ℤ/⟨ n ⟩
  π = ∫hom [_] π-hom
  module π = is-ring-hom π-hom
```

The underlying function of $\pi$ has a section `σ`{.Agda}.

```agda
  σ : Fin n → Int
  σ (fin x) = pos x

  σ-is-section : ∀ x → [ σ x ] ≡ x
  σ-is-section x = fin-ap (Fin-%ℤ x)
```

The ring $\ZZ_n$ together with the homomorphism $\pi$ form the [[quotient
ring]] of $\ZZ$ by the [[principal ideal]] $(n) = \ZZ \cdot n$.

<!--
```agda
module _ (n) ⦃ _ : Positive n ⦄ where
  private module ℤₙ = Rr ℤ/⟨ n ⟩
```
-->

```agda
  ⟨_⟩ℤ : ℙ ⌞ ℤ ⌟
  ⟨_⟩ℤ x = elΩ (Σ[ y ∈ ℤ ] x ≡ y *ℤ pos n)
```

This is proven by showing $\pi$ has the required universal property.
First note that $\pi$ sends $(n)$ to zero.

```agda
  private
    ⟨n⟩ℤ→0 : I→0 ℤ ⟨_⟩ℤ π
    ⟨n⟩ℤ→0 = elim! λ q x≡qn →
      fin-ap (ap (_%ℤ n) (x≡qn ∙ sym (+ℤ-zeror _)) ∙ %ℤ-clear n q 0) ∙ %ᶠ-pres-0
```

Suppose $f : \ZZ \to S$ is a ring homomorphism such that $f(n) = 0$. We
construct the factorization $f' : \ZZ_n \to S$ as follows:

<!--
```agda
  private module _ {S} (f : Rings.Hom ℤ S) (fI→0 : I→0 ℤ ⟨_⟩ℤ f) where
    module S = Rr S
    module f = is-ring-hom (f .snd)
```agda
-->

```agda
    f' : Fin n → ⌞ S ⌟
    f' x = f · (σ x)

    f'[x]≡fx : ∀ x → f' [ x ] ≡ f · x
    f'[x]≡fx x =
      f · pos (x %ℤ n)                           ≡⟨ S.a.introl (fI→0 (inc (x /ℤ n , refl))) ⟩
      f · (x /ℤ n *ℤ pos n) S.+ f · pos (x %ℤ n) ≡˘⟨ f.pres-+ (x /ℤ n *ℤ pos n) (pos (x %ℤ n)) ⟩
      f · (x /ℤ n *ℤ pos n +ℤ pos (x %ℤ n))      ≡˘⟨ ap· f $ is-divmodℤ x n ⟩
      f · x                                      ∎
```

Exploiting the section $\sigma$, we can show that $f'$ is indeed a ring
homomorphism.

```agda
    f'-is-hom : is-ring-hom (ℤ/⟨ n ⟩ .snd) (S .snd) f'
    f'-is-hom = let open is-ring-hom in λ where
      .pres-id → f'[x]≡fx 1 ∙ f.pres-id
      .pres-* x y →
        f' ( x ℤₙ.* y)            ≡˘⟨ ap f' $ ap₂ ℤₙ._*_ (σ-is-section x) (σ-is-section y) ⟩
        f' ([ σ x ] ℤₙ.* [ σ y ]) ≡˘⟨ ap f' (π.pres-* (σ x) (σ y)) ⟩
        f' [ σ x *ℤ σ y ]         ≡⟨ f'[x]≡fx (σ x *ℤ σ y) ⟩
        f · (σ x *ℤ σ y)          ≡⟨ (f.pres-* (σ x) (σ y)) ⟩
        f' x S.* f' y             ∎
      .pres-+ x y →
        f' (x ℤₙ.+ y)             ≡˘⟨ ap f' $ ap₂ ℤₙ._+_ (σ-is-section x) (σ-is-section y) ⟩
        f' ([ σ x ] ℤₙ.+ [ σ y ]) ≡˘⟨ ap f' (π.pres-+ (σ x) (σ y)) ⟩
        f' [ σ x +ℤ σ y ]         ≡⟨ f'[x]≡fx (σ x +ℤ σ y) ⟩
        f · (σ x +ℤ σ y)          ≡⟨ (f.pres-+ (σ x) (σ y)) ⟩
        f' x S.+ f' y             ∎

    f'-hom : Rings.Hom ℤ/⟨ n ⟩ S
    f'-hom = ∫hom f' f'-is-hom
```

Moreover, $f'$ is the unique such factorisation: Given any other
homomorphism $h : \ZZ_n \to S$ for which $h \circ \pi = f$, it follows
that $f'(x) = f(\sigma(x)) = h [\sigma(x)] = h(x)$.

```agda
    f'-unique : ∀ {h : Rings.Hom ℤ/⟨ n ⟩ S} (p : h Rings.∘ π ≡ f) → f'-hom ≡ h
    f'-unique {h} p = ext λ x →
      f' x        ≡˘⟨ p ·ₚ (σ x) ⟩
      h · [ σ x ] ≡⟨ (ap· h $ σ-is-section x) ⟩
      h · x       ∎

  ℤ/⟨_⟩-is-quotient : is-quotient-ring ℤ ⟨_⟩ℤ (π {n})
  ℤ/⟨_⟩-is-quotient = let open is-quotient-ring in λ where
    .πI→0 → ⟨n⟩ℤ→0
    .universal → f'-hom
    .factors → ℤ-is-initial.¡-unique₂ _ _
    .unique {f = f} {fI→0} → f'-unique f fI→0
```
