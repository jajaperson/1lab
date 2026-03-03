<!--
```agda
open import 1Lab.Function.Surjection
open import 1Lab.Function.Embedding
open import 1Lab.Equiv.Fibrewise using (_≃[_]_)
open import 1Lab.Equiv
open import 1Lab.Function.Fibrewise
open import 1Lab.Path
open import 1Lab.Type.Sigma
open import 1Lab.Type
```
-->

```agda
module 1Lab.Function.Fibrewise.Properties 
  {ℓa ℓb ℓp ℓq} {A : Type ℓa} {B : Type ℓb} {P : A → Type ℓp} {Q : B → Type ℓq}
  where
```

<!--
```agda
private variable f : A → B
```
-->

# Properties of functions over

We can generalise the properties of being [[injective]], [[surjective]], 
or an [equivalence] to functions over:

[equivalence]: 1Lab.Equiv.html

```agda
injective-over : P -[ f ]→ Q → Type _
injective-over f' = ∀ a b p → injective (f' a b p)

is-surjective-over : P -[ f ]→ Q → Type _
is-surjective-over f' = ∀ a b p → is-surjective (f' a b p)

is-equiv-over : P -[ f ]→ Q → Type _
is-equiv-over f' = ∀ a b p → is-equiv (f' a b p)
```

To prove any of these, it suffices to prove the case for $f_{a, f(a), \rm{refl}}$

```agda
injective→injective-over 
  : ∀ {f' : P -[ f ]→ Q}
  → (∀ a → injective (f' a (f a) refl))
  → injective-over f'
injective→injective-over {f' = f'} inj a b = 
  J (λ y p → injective (f' a y p)) (inj a)

is-surjective→is-surjective-over
  : ∀ {f' : P -[ f ]→ Q}
  → (∀ a → is-surjective (f' a (f a) refl))
  → is-surjective-over f'
is-surjective→is-surjective-over {f' = f'} surj a b =
  J (λ y p → is-surjective (f' a y p)) (surj a)

is-equiv→is-equiv-over
  : ∀ {f' : P -[ f ]→ Q}
  → (∀ a → is-equiv (f' a (f a) refl))
  → is-equiv-over f'
is-equiv→is-equiv-over {f' = f'} eqv a b =
  J (λ y p → is-equiv (f' a y p)) (eqv a)
```

Being an equivalence over a $f$ implies being both injective and
surjective over $f$, as well as the existence of an inverse:

```agda
is-equiv-over→injective-over 
  : ∀ {f' : P -[ f ]→ Q} 
  → is-equiv-over f' → injective-over f'
is-equiv-over→injective-over {f' = f'} eqv' a b p = 
  Equiv.injective (f' a b p , eqv' a b p)

is-equiv-over→is-surjective-over 
  : ∀ {f' : P -[ f ]→ Q} 
  → is-equiv-over f' → is-surjective-over f'
is-equiv-over→is-surjective-over {f' = f'} eqv' a b p = 
  is-equiv→is-surjective (eqv' a b p)
```

## Relation to equivalences over

When we are dealing with a function over an equivalence, having the 
property `is-equiv-over`{.Agda} amounts to being an [[equivalence over]]:

```agda
module _ {e : A ≃ B} where
  private module e = Equiv e
  private map-over+equiv = Σ (P -[ e.to ]→ Q) λ e' → is-equiv-over e'

  map-over→equiv-over 
    :  ∀ (e' : P -[ e.to ]→ Q) 
    → is-equiv-over e' → P ≃[ e ] Q
  map-over→equiv-over e' e'-eqv a b p = e' a b p , e'-eqv a b p

  equiv-over→map-over : P ≃[ e ] Q → map-over+equiv
  equiv-over→map-over e' = (λ a b p → e' a b p .fst) , λ a b p → e' a b p .snd

  map-over≃equiv=over : map-over+equiv ≃ (P ≃[ e ] Q)
  map-over≃equiv=over = Iso→Equiv
    (uncurry map-over→equiv-over , iso equiv-over→map-over (λ _ → refl) λ _ → refl)

  module map-over≃equiv=over = Equiv map-over≃equiv=over
```

We can also generalise `equiv→inverse`{.Agda}:

```agda
  equiv-over→inverse-over 
    : {e' : P -[ e.to ]→ Q} → is-equiv-over e' 
    → Q -[ e.from ]→ P
  equiv-over→inverse-over eqv' b a p b' = equiv→inverse 
    (eqv' a b (e.adjunctr (sym p))) b'
  
  equiv-over→counit-over
    : {e' : P -[ e.to ]→ Q} → (eqv' : is-equiv-over e')
    → ∀ a b p b'
    → e' a b p (equiv-over→inverse-over eqv' b a (sym (e.adjunctl p)) b') ≡ b'
  equiv-over→counit-over {e' = e'} eqv' a b p b' = ε' where
    ε' : e' a b p (equiv→invere (eqv' a b (e.adjunctr (e.adjunctl p))) b') ≡ b'
    ε' = subst 
      (λ q → e' a b p (equiv→inverse (eqv' a b q) b') ≡ b') 
      (sym (Equiv.η e.adjunct p)) 
      (equiv→counit (eqv' a b p) b')

  equiv-over→unit-over  
    : {e' : P -[ e.to ]→ Q} → (eqv' : is-equiv-over e')
    → ∀ a b p a'
    → equiv→inverse (eqv' a b (e.adjunctr (e.adjunctl p))) (e' a b p a') ≡ a'
  equiv-over→unit-over {e' = e'} eqv' a b p a' = η' where
    η' : equiv→inverse (eqv' a b (e.adjunctr (e.adjunctl p))) (e' a b p a') ≡ a'
    η' = subst 
      (λ q → equiv→inverse (eqv' a b q) (e' a b p a') ≡ a')  
      (sym (Equiv.η e.adjunct p)) 
      (equiv→unit (eqv' a b p) a')
```