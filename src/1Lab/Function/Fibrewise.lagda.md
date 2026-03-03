<!--
```agda
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Function.Fibrewise where
```

# Fibrewise maps {defines="fibrewise-map fibrewise-function"}

In HoTT, a type family `P : A → Type` can be seen as a [_fibration_]
with total space `Σ P`, with the fibration being the projection
`fst`{.Agda}. Because of this, a function with type `(x : _) → P x → Q
x` can be referred as a **fibrewise map**.

[_fibration_]: https://ncatlab.org/nlab/show/fibration

A function like this can be lifted to a function on total spaces:

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B : Type ℓ
  P Q : A → Type ℓ
```
-->

```agda
total : ((x : A) → P x → Q x)
      → Σ A P → Σ A Q
total f (x , y) = x , f x y
```

Furthermore, the fibres of `total f` correspond to fibres of f, in the
following manner:

```agda
total-fibres : {f : (x : A) → P x → Q x} {x : A} {v : Q x}
             → Iso (fibre (f x) v) (fibre (total f) (x , v))
total-fibres {A = A} {P = P} {Q = Q} {f = f} {x = x} {v = v} = the-iso where

  to : {x : A} {v : Q x} → fibre (f x) v → fibre (total f) (x , v)
  to (v' , p) = (_ , v') , λ i → _ , p i

  from : {x : A} {v : Q x} → fibre (total f) (x , v) → fibre (f x) v
  from ((x , v) , p) = transport (λ i → fibre (f (p i .fst)) (p i .snd)) (v , refl)

  the-iso : {x : A} {v : Q x} → Iso (fibre (f x) v) (fibre (total f) (x , v))
  the-iso .fst = to
  the-iso .snd .is-iso.from = from
  the-iso .snd .is-iso.rinv ((x , v) , p) =
    J (λ { _ p → to (from ((x , v) , p)) ≡ ((x , v) , p) })
      (ap to (J-refl {A = Σ A Q} (λ { (x , v) _ → fibre (f x) v } ) (v , refl)))
      p
  the-iso .snd .is-iso.linv (v , p) =
    J (λ { _ p → from (to (v , p)) ≡ (v , p) })
      (J-refl {A = Σ A Q} (λ { (x , v) _ → fibre (f x) v } ) (v , refl))
      p
```

# Map over {defines="function-over map-over"}

We can generalise the notion of [[fibrewise function]] to families
$P : A \to \ty$, $Q : B \to \ty$ over _different_ base types, provided
we have a function $f : A \to B$.

Let $A$ and $B$ be types, $a : A \vdash P(a)$ and $b : B \vdash Q(b)$ be
type families, and $f : A \to B$ be a function. A **map over** $f$
consists of a function $f'_{a, b, p} : P(a) \to P(b)$ for every pair of
points $a : A, b : B$ with a path $p : f(a) \equiv_B b$.

```agda
_-[_]→_
  : ∀ (P : A → Type ℓ) (f : A → B) (Q : B → Type ℓ') → Type _
_-[_]→_ {A = A} {B = B} P f Q = ∀ (a : A) (b : B) → f a ≡ b → (P a → Q b)
```

<!--
```agda
module _ {P : A → Type ℓ}  {Q : B → Type ℓ'} where
  private variable f : A → B
```
-->

Allowing the mapping behaviour depend on the path $p : f(a) \equiv_B b$
like this may at first seem too general, but the [[contractibility of 
singletons]] forces $f'_{a,a,\rm{refl}}$ and $f'_{a,b,p}$ to agree in 
the following sense:

```agda
  _ : ∀ f (f' : P -[ f ]→ Q)
    → ∀ a b (p : f a ≡ b)
    → ∀ a' → subst Q p (f' a (f a) refl a') ≡ f' a b p a'
  _ = λ f f' a b p a' → J
    (λ y q → subst Q q (f' a (f a) refl a') ≡ f' a y q a') 
    (transport-refl (f' a (f a) refl a')) p
```

A function over $f$ induces a function between total spaces

```agda
  map-over→total : P -[ f ]→ Q → Σ A P → Σ B Q
  map-over→total {f = f} f' (a , a') = (f a) , f' a (f a) refl a'
```

Here, conceptual meaning of `P -[ f ]→ Q`{.Agda ident="_-[_]→_"} is made
more clear by the commutativity of the diagram

~~~{.quiver .attach-around}
\begin{tikzcd}
	{\sum_{a:A}P(a)} && {\sum_{b:B}Q(b)} \\
	\\
	A && B
	\arrow["{\sum f'}", from=1-1, to=1-3]
	\arrow["{\text{fst}}"', two heads, from=1-1, to=3-1]
	\arrow["{\text{fst}}", two heads, from=1-3, to=3-3]
	\arrow["f"', from=3-1, to=3-3]
\end{tikzcd}
~~~

where $\sum f'$ denotes `map-over→total f'`{.Agda ident="map-over→total"}.

<!--
```agda
  module _ {f' : P -[ f ]→ Q} where
```
-->

```agda
    _ : f ∘ fst ≡ fst ∘ map-over→total f'
    _ = refl
```

Usually we can construct a function over $f$ from functions 
$f'_a : P(a) \to Q(f(a))$ for each $a$, i.e. the case where 
$f(a) = b$ _definitionally_.

```agda
  over-left→map-over : (∀ (a : A) → P a → Q (f a)) → P -[ f ]→ Q
  over-left→map-over f' a b p a' = subst Q  p (f' a a')
```
