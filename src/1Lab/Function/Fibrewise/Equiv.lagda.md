<!--
```agda
open import 1Lab.Function.Fibrewise
open import 1Lab.Equiv.Fibrewise
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type.Sigma
open import 1Lab.Type
```
-->

```agda
module 1Lab.Function.Fibrewise.Equiv 
  {ℓa ℓb ℓp ℓq} {A : Type ℓa} {B : Type ℓb} {P : A → Type ℓp} {Q : B → Type ℓq}
  where
```

<!--
```agda
private variable f : A → B
```
-->

# Equivalences over functions

We can generalize the property `is-equiv`{.Agda} to a [[function over]]:

```agda
is-equiv-over : P -[ f ]→ Q → Type _
is-equiv-over f' = ∀ a b p → is-equiv (f' a b p)
```

To prove a function over $f$ is an equivalence over $f$, it suffices to
prove the case for $f_{a, f(a), \rm{refl}}$:

```agda
is-equiv→is-equiv-over
  : ∀ {f' : P -[ f ]→ Q}
  → (∀ a → is-equiv (f' a (f a) refl))
  → is-equiv-over f'
is-equiv→is-equiv-over {f' = f'} eqv a b =
  J (λ y p → is-equiv (f' a y p)) (eqv a)
```

## Equivalences over equivalences

<!--
```agda
_ = _≃[_]_ -- for inline code

module _ {e : A ≃ B} where
  private module e = Equiv e
```
-->

This differs very slightly from out other notion of [[equivalence over]]
in that we don't require the base function $f$ to be an equivalence.
Given an equivalence `e`, the type `P ≃[ e ] Q`{.Agda ident="_≃[_]_"} is
equivalent to the type

```agda
  map-over+equiv = Σ (P -[ e.to ]→ Q) λ e' → is-equiv-over e'
```

by

```agda
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
    ε' : e' a b p (equiv→inverse (eqv' a b (e.adjunctr (e.adjunctl p))) b') ≡ b'
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