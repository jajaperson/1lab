<!--
```agda
open import Algebra.Magma

open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Adjoint
open import Cat.Prelude
```
-->

```agda
module Algebra.Magma.Free where
```

<!--
```agda
private variable
  ℓ : Level
  A B C : Type ℓ
```
-->

# Free magmas {defines=free-magma}

The underlying type of a free magma on $A$ can be thought of as
consisting of _fully parenthesized words_, e.g. $(x((yz)w)t)$. We can
implement this as the following inductive type:

```agda
data Paren-word (A : Type ℓ) : Type ℓ where
  inc : A → Paren-word A
  _⋆_ : Paren-word A → Paren-word A → Paren-word A
```

`Paren-word`{.Agda} is functorial in the handwavy sense of supporting a
`map` operation.

```agda
Paren-word-map : (f : A → B) → Paren-word A → Paren-word B
Paren-word-map f (inc a) = inc (f a)
Paren-word-map f (x ⋆ y) = (Paren-word-map f x) ⋆ (Paren-word-map f y)

Paren-word-map-id
  : (x : Paren-word A) → Paren-word-map (λ x → x) x ≡ x
Paren-word-map-id (inc b) = refl
Paren-word-map-id (x ⋆ y) = ap₂ _⋆_ (Paren-word-map-id x) (Paren-word-map-id y)

Paren-word-map-∘
  : ∀ (f : B → C) (g : A → B) x
  → Paren-word-map (f ⊙ g) x ≡ (Paren-word-map f ⊙ Paren-word-map g) x
Paren-word-map-∘ f g (inc b) = refl
Paren-word-map-∘ f g (x ⋆ y) = ap₂ _⋆_ (Paren-word-map-∘ f g x) (Paren-word-map-∘ f g y)
```

To characterize paths in `Paren-word`{.Agda} we construct the following
[[identity system]].

```agda
module _ {A : Type ℓ} where
  module Paren-word-path where
    Code : Paren-word A → Paren-word A → Type ℓ
    Code (inc a) (inc b) = a ≡ b
    Code (inc _) (_ ⋆ _) = Lift ℓ ⊥
    Code (_ ⋆ _) (inc _) = Lift ℓ ⊥
    Code (x ⋆ y) (z ⋆ w) = (Code x z) × (Code y w)

    Code-is-hlevel
      : ∀ n → is-hlevel A (2 + n)
      → ∀ x y → is-hlevel (Code x y) (1 + n)
    Code-is-hlevel n ah (inc a) (inc b) = ah a b
    Code-is-hlevel n ah (_ ⋆ _) (inc _) = hlevel (1 + n)
    Code-is-hlevel n ah (inc _) (_ ⋆ _) = hlevel (1 + n)
    Code-is-hlevel n ah (x ⋆ y) (z ⋆ w) = ×-is-hlevel (1 + n)
      (Code-is-hlevel n ah x z) (Code-is-hlevel n ah y w)

    Code-refl : ∀ x   → Code x x
    Code-refl (inc a) = refl
    Code-refl (x ⋆ y) = (Code-refl x) , (Code-refl y)

    decode : ∀ {x y} → Code x y → x ≡ y
    decode {inc a} {inc b} code = ap inc code
    decode {x ⋆ y} {z ⋆ w} code = ap₂ _⋆_ (decode (code .fst)) (decode (code .snd))

    ids : is-identity-system Code Code-refl
    ids .to-path = decode
    ids .to-path-over {inc _} {inc _} p i j = p (i ∧ j)
    ids .to-path-over {_ ⋆ _} {_ ⋆ _} (p , q) i =
      ids .to-path-over p i , ids .to-path-over q i

    Code≃Path : ∀ {x y} → (x ≡ y) ≃ Code x y
    Code≃Path = identity-system-gives-path ids e⁻¹

  open Paren-word-path

  Paren-word-is-hlevel : ∀ n → is-hlevel A (2 + n) → is-hlevel (Paren-word A) (2 + n)
  Paren-word-is-hlevel n ah = identity-system→hlevel (1 + n) ids (Code-is-hlevel n ah)
```

<!--
```agda
  instance
    H-Level-Paren-word
      : ∀ {n} ⦃ _ : H-Level A (2 + n) ⦄ → H-Level (Paren-word A) (2 + n)
    H-Level-Paren-word {n} .H-Level.has-hlevel = Paren-word-is-hlevel n (hlevel (2 + n))
```
-->

We can now show that if $A$ is a set, then so is `Paren-word`{.Agda},
and thus `_⋆_`{.Agda} endows $A$ with the structure of a [[magma]].

```agda
module _ (a-s : is-set A) where
  is-set→Paren-word-is-set : is-set (Paren-word A)
  is-set→Paren-word-is-set = Paren-word-is-hlevel 0 a-s

  is-set→Paren-word-is-magma : is-magma (Paren-word._⋆_ {A = A})
  is-set→Paren-word-is-magma = record { has-is-set = is-set→Paren-word-is-set }

Free-Magma : Set ℓ → Magma ℓ
Free-Magma A .fst = el! (Paren-word ⌞ A ⌟)
Free-Magma A .snd = record
  { _⋆_ = _⋆_
  ; has-is-magma = is-set→Paren-word-is-magma (A .is-tr)
  }
```

Free-magma : Functor (Sets ℓ) (Magmas ℓ)
Free-magma .F₀ A .fst = el! (Paren-word ⌞ A ⌟)
Free-magma .F₀ A .snd = record
  { _⋆_ = _⋆_
  ; has-is-magma = is-set→Paren-word-is-magma (hlevel 2)
  }
Free-magma .F₁ f .fst = Paren-word-map f
Free-magma .F₁ f .snd _ _ = refl
Free-magma .F-id = ext Paren-word-map-id
Free-magma .F-∘ f g = ext (Paren-word-map-∘ f g)


## Universal property

The `Free-magmas`{.Agda}, or more specifically, the map `inc`{.Agda}
satisfies the universal property of a [[free object]], relative to the
forgetful functor `Magmas↪Set`. To establish this result, we first
implement a helper function `fold-free-magma`{.Agda}, which, given the
data of where to send the generators of a free magma determines a magma
homomorphism. Compared with the [[group case|free group]], it's a walk
in the park.

```agda
fold-free-magma
  : (A : Set ℓ) (M : Magma ℓ)
  → (⌞ A ⌟ → ⌞ M ⌟) → Magmas.Hom (Free-Magma A) M
fold-free-magma A M f = ∫hom f♯ (λ _ _ → refl) where
  module M = Magma-on (M .snd)

  f♯ : ⌞ Free-Magma · A ⌟ → ⌞ M ⌟
  f♯ (inc a) = f a
  f♯ (x ⋆ y) = (f♯ x) M.⋆ (f♯ y)
```

<!--
```agda
open Free-object
```
-->

```agda
make-free-magma : ∀ {ℓ} (A : Set ℓ) → Free-object Magmas↪Sets A
make-free-magma A .free = Free-Magma A
make-free-magma A .unit = inc
make-free-magma A .fold {M} = fold-free-magma A M
make-free-magma A .commute = refl
make-free-magma A .unique {M} {f} g p = ext q where
  module M = Magma-on (M .snd)
  f♯ = fold-free-magma A M f
  
  q : ∀ x → f♯ · x ≡ g · x
  q (inc a) = sym p ·ₚ a
  q (x ⋆ y) = f♯ .snd x y ∙∙ ap₂ M._⋆_ (q x) (q y) ∙∙ sym (g .snd x y)
```

Thus in particular `Magmas↪Sets`{.Agda} has a left adjoint functor,
`Free-magma`{.Agda}

```agda
Free-magma : Functor (Sets ℓ) (Magmas ℓ)
Free-magma = free-objects→functor make-free-magma

Free-magma⊣U : Free-magma {ℓ} ⊣ Magmas↪Sets
Free-magma⊣U = free-objects→left-adjoint make-free-magma
```
