<!--
```agda
open import 1Lab.Function.Fibrewise.Equiv
open import 1Lab.Equiv
open import 1Lab.Function.Embedding
open import 1Lab.Function.Fibrewise
open import 1Lab.Type
open import 1Lab.Path
```
-->

```agda
module 1Lab.Function.Fibrewise.Injection 
  {ℓa ℓb ℓp ℓq} {A : Type ℓa} {B : Type ℓb} {P : A → Type ℓp} {Q : B → Type ℓq}
  where
```

<!--
```agda
private variable f : A → B
```
-->

# Injections over {defines="injective-over"}

We can generalize the property of being `injective`{.Agda} to a
[[function over]]:

```agda
injective-over : P -[ f ]→ Q → Type _
injective-over f' = ∀ a b p → injective (f' a b p)
```

To prove a function over $f$ is injective over $f$, it suffices to prove
the case for $f_{a, f(a), \rm{refl}}$:

```agda
injective→injective-over 
  : ∀ {f' : P -[ f ]→ Q}
  → (∀ a → injective (f' a (f a) refl))
  → injective-over f'
injective→injective-over {f' = f'} inj a b = 
  J (λ y p → injective (f' a y p)) (inj a)
```

Being injective over $f$ is implied by being an equivalence over $f$:

```agda
is-equiv-over→injective-over 
  : ∀ {f' : P -[ f ]→ Q} 
  → is-equiv-over f' → injective-over f'
is-equiv-over→injective-over {f' = f'} eqv' a b p = 
  Equiv.injective (f' a b p , eqv' a b p)
```