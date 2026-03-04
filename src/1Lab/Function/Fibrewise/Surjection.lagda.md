<!--
```agda
open import 1Lab.Function.Fibrewise.Equiv
open import 1Lab.Function.Fibrewise
open import 1Lab.Function.Surjection
open import 1Lab.Type
open import 1Lab.Path
```
-->

```agda
module 1Lab.Function.Fibrewise.Surjection
  {ℓa ℓb ℓp ℓq} {A : Type ℓa} {B : Type ℓb} {P : A → Type ℓp} {Q : B → Type ℓq}
  where
```

<!--
```agda
private variable f : A → B
```
-->

# Surjections over {defines="surjective-over"}

We can generalize the property `is-surjective`{.Agda} to a [[function
over]]:

```agda
is-surjective-over : P -[ f ]→ Q → Type _
is-surjective-over f' = ∀ a b p → is-surjective (f' a b p)
```

To prove a function over $f$ is surjective over $f$, it suffices to 
prove the case for $f_{a, f(a), \rm{refl}}$:

```agda
is-surjective→is-surjective-over
  : ∀ {f' : P -[ f ]→ Q}
  → (∀ a → is-surjective (f' a (f a) refl))
  → is-surjective-over f'
is-surjective→is-surjective-over {f' = f'} surj a b =
  J (λ y p → is-surjective (f' a y p)) (surj a)
```

eing surjective over $f$ is implied by being an equivalence over $f$:

```agda
is-equiv-over→is-surjective-over 
  : ∀ {f' : P -[ f ]→ Q} 
  → is-equiv-over f' → is-surjective-over f'
is-equiv-over→is-surjective-over {f' = f'} eqv' a b p = 
  is-equiv→is-surjective (eqv' a b p)
```