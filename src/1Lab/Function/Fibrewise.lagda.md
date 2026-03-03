<!--
```agda
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Function.Fibrewise where
```

# Function over {defines="function-over"}

In the same way that an [[equivalence over]] generalises a [[fibrewise
equivalence]], we can generalise a [[fibrewise map]] to type families
with different base types.

Let $A$ and $B$ be types, $a : A \vdash P(a)$ and $b : B \vdash Q(b)$ be
type families, and $f : A \to B$ be a function. A **function over** $f$
consists of a function $f'_{a, b, p} : P(a) \to P(b)$ for every pair of
points $a : A, b : B$ with a path $p : f(a) \equiv_B b$.

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B : Type ℓ
  P Q : A → Type ℓ
```
-->

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
  over→total : P -[ f ]→ Q → Σ A P → Σ B Q
  over→total {f = f} f' (a , a') = (f a) , f' a (f a) refl a'
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

where $\sum f'$ denotes `over→total f'`{.Agda ident="over→total"}.

<!--
```agda
  module _ {f' : P -[ f ]→ Q} where
```
-->

```agda
    _ : f ∘ fst ≡ fst ∘ over→total f'
    _ = refl
```

Usually we can construct a function over $f$ from functions 
$f'_a : P(a) \to Q(f(a))$ for each $a$, i.e. the case where 
$f(a) = b$ _definitionally_.

```agda
  over-left→over : (∀ (a : A) → P a → Q (f a)) → P -[ f ]→ Q
  over-left→over f' a b p a' = subst Q  p (f' a a')
```
