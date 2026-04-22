<!--
```agda
open import Cat.Displayed.Functor.Equivalence
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Equivalence
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.Path where

open Precategory
open Displayed
```

# Paths of displayed categories

If you have a pair of [[displayed categories]] $\cE \liesover \cB_0$ and
$\cF \liesover \cB_1$ over a line of precategories $\cB_i, i : \II$, it
might be interesting --- if you, like me, are a lunatic --- to know when
they can be connected by a `PathP`{.Agda} over $\cB$. This module
answers that! A path between displayed categories, over a path of their
corresponding bases, is a [[displayed functor]]

~~~{.quiver}
\[\begin{tikzcd}
  {\mathcal{E}} && {\mathcal{F}} \\
  \\
  {\mathcal{B}_0} && {\mathcal{B}_1}
  \arrow["{\mathrm{path}(\mathcal{B})}"', from=3-1, to=3-3]
  \arrow["F", from=1-1, to=1-3]
  \arrow[lies over, from=1-1, to=3-1]
  \arrow[lies over, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

which is componentwise an equivalence.

<!--
```agda
private
  module
    _ {o ℓ o' ℓ'} {B : I → Precategory o ℓ}
      {E : Displayed (B i0) o' ℓ'}
      {F : Displayed (B i1) o' ℓ'}
    where
    private
      module E = Displayed E
      module F = Displayed F
```
-->

## The first step

We write this proof in two steps: First, we write a helper function
which abstracts over the contentful part of the path (the displayed
object spaces, displayed Hom spaces, etc) and automatically fills in the
proofs that the _laws_ are preserved. We have a record
`displayed-pathp-data`{.Agda} which contains paths for all the
interesting components:

```agda
    record displayed-pathp-data : Type (lsuc (o ⊔ ℓ ⊔ o' ⊔ ℓ')) where
      no-eta-equality
      field
        obp  : PathP (λ i → B i .Ob → Type o') E.Ob[_] F.Ob[_]
        homp : PathP
          (λ i → {x y : B i .Ob} (f : B i .Hom x y) → obp i x → obp i y → Type ℓ')
          E.Hom[_] F.Hom[_]
```

The types get increasingly unhinged as we go: The identification between
displayed object spaces lies over the identification of objects of the
underlying category; the identification between displayed Hom spaces
lies over a path in the base category _and_ the path of displayed object
spaces we just defined.

The paths between the identity morphisms and composite morphisms lie
over _both_ of those, _and_ they have to quantify over _every_ implicit
argument _inside_ the path! That's why this record is in a private
helper module, you see.

```agda
        idp : PathP (λ i → ∀ {x} {x' : obp i x} → homp i (B i .id) x' x') E.id' F.id'
        compp : PathP
          (λ i → ∀ {x y z}    {f : B i .Hom y z}    {g : B i .Hom x y}
               → ∀ {x' y' z'} (f' : homp i f y' z') (g' : homp i g x' y')
               → homp i (B i ._∘_ f g) x' z')
          E._∘'_ F._∘'_
        hom[]p : PathP
          (λ i → {a b : B i .Ob} {x : obp i a} {y : obp i b} {f g : B i .Hom a b}
               → (p : f ≡ g) (f' : homp i f x y) → homp i g x y)
          E.hom[_] F.hom[_]
```

An instance of this record determines a path of displayed categories,

```agda
    displayed-pathp-worker
      : displayed-pathp-data → PathP (λ i → Displayed (B i) o' ℓ') E F
    displayed-pathp-worker input = go where
      open displayed-pathp-data input
```

such that all the interesting components are literal, and the coherence
components are, by definition, unimportant.

<!--
```agda
      homp-set :
        PathP
          (λ i → (a b : B i .Ob) (f : B i .Hom a b) (x : obp i a) (y : obp i b) → is-set (homp i f x y))
          (λ a b → E .Hom[_]-set) λ a b → F .Hom[_]-set
      homp-set i a b f x y = is-prop→pathp
        (λ i    → Π-is-hlevel³ {A = B i .Ob} {B = λ _ → B i .Ob} {C = λ a b → B i .Hom a b} 1
          λ a b f → Π-is-hlevel² {A = obp i a} {B = λ _ → obp i b} 1
          λ x y   → is-hlevel-is-prop {A = homp i f x y} 2)
        (λ _ _ → E .Hom[_]-set) (λ _ _ → F .Hom[_]-set) i a b f x y
```
-->

```agda
      go : PathP (λ i → Displayed (B i) o' ℓ') E F
      go i .Ob[_] x = obp i x
      go i .Hom[_]  = homp i
      go i .Hom[_]-set {a} {b} f x y = homp-set i a b f x y
      go i .id' = idp i
      go i ._∘'_ = compp i
```

<!--
```agda
      go i .idr' {a} {b} {x} {y} {f} f' j = is-set→squarep
        (λ i j     → Π-is-hlevel³ {A = B i .Ob} {B = λ _ → B i .Ob}      {C = λ a _ → obp i a}      2
          λ a b x  → Π-is-hlevel³ {A = obp i b} {B = λ _ → B i .Hom a b} {C = λ y f → homp i f x y} 2
          λ y f f' → homp-set i a b (B i .idr f j) x y)
        (λ i a b x y f f' → compp i f' (idp i))
        (λ i a b x y f f' → E .idr' f' i)
        (λ i a b x y f f' → F .idr' f' i)
        (λ i a b x y f f' → f')
        i j a b x y f f'
      go i .idl' {a} {b} {x} {y} {f} f' j = is-set→squarep
        (λ i j     → Π-is-hlevel³ {A = B i .Ob} {B = λ _ → B i .Ob}      {C = λ a _ → obp i a}      2
          λ a b x  → Π-is-hlevel³ {A = obp i b} {B = λ _ → B i .Hom a b} {C = λ y f → homp i f x y} 2
          λ y f f' → homp-set i a b (B i .idl f j) x y)
        (λ i a b x y f f' → compp i (idp i) f')
        (λ i a b x y f f' → E .idl' f' i)
        (λ i a b x y f f' → F .idl' f' i)
        (λ i a b x y f f' → f')
        i j a b x y f f'
      go i .assoc' {a} {b} {c} {d} {w} {x} {y} {z} {f} {g} {h} f' g' h' j = is-set→squarep
        (λ i j     → Π-is-hlevel³ {A = B i .Ob}      {B = λ _ → B i .Ob}      {C = λ _ _ → B i .Ob}      2
          λ a b c  → Π-is-hlevel³ {A = B i .Ob}      {B = λ _ → obp i a}      {C = λ _ _ → obp i b}      2
          λ d w x  → Π-is-hlevel³ {A = obp i c}      {B = λ _ → obp i d}      {C = λ _ - → B i .Hom c d} 2
          λ y z f  → Π-is-hlevel³ {A = B i .Hom b c} {B = λ _ → B i .Hom a b} {C = λ _ _ → homp i f y z} 2
          λ g h f' → Π-is-hlevel² {A = homp i g x y} {B = λ _ → homp i h w x}                            2
          λ g' h'  → homp-set i a d (B i .assoc f g h j) w z)
        (λ i a b c d w x y z f g h f' g' h' → compp i f' (compp i g' h'))
        (λ i a b c d w x y z f g h f' g' h' → E .assoc' f' g' h' i)
        (λ i a b c d w x y z f g h f' g' h' → F .assoc' f' g' h' i)
        (λ i a b c d w x y z f g h f' g' h' → compp i (compp i f' g') h')
        i j a b c d w x y z f g h f' g' h'
      go i .hom[_] {a} {b} {x} {y} {f} {g} p f' = hom[]p i p f'
      go i .coh[_] {a} {b} {x} {y} {f} {g} p f' j = is-set→squarep
        (λ i j → Π-is-hlevel² {A = B i .Ob} {B = λ _ → B i .Ob} 2
         λ a b → Π-is-hlevel² {A = obp i a} {B = λ _ → obp i b} 2
         λ x y → Π-is-hlevel³ {A = B i .Hom a b} {B = λ f → B i .Hom a b} {C = λ f g → f ≡ g} 2
         λ f g p → Π-is-hlevel {A = homp i f x y} 2 λ f' →
          homp-set i a b (p j) x y
         )
          (λ i x y a b f g p f' → f')
          (λ i x y a b f g p f' → E.coh[ p ] f' i)
          (λ i x y a b f g p f' → F.coh[ p ] f' i)
          (λ i x y a b f g p f' → hom[]p i p f')
          i j a b x y f g p f'
```
-->

## Complicating it

Suppose that we have $\cE \liesover \cB$ and $\cF \liesover
\cC$, together with a functor $F : \cB \to \cC$ which is an
[isomorphism of precategories], and a functor $G : \cE \to \cF$ over $F$
which is a [[isomorphism of displayed precategories]] This is the
situation in the introduction, but where the line $\cB_i$ comes from the
[[identity system]] on precategories given by isomorphisms of
precategories.

[isomorphism of precategories]: Cat.Functor.Equivalence.html#isomorphisms

<!--
```agda
module
  _ {o ℓ o' ℓ'} {B C : Precategory o ℓ} (F : Functor B C)
    {ℰ : Displayed B o' ℓ'} {ℱ : Displayed C o' ℓ'}
    (G : Displayed-functor F ℰ ℱ)
  where
  private
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ
    module G = Displayed-functor G
    module C = Precategory C
    module F = Functor F
```
-->

The functor $G$ must be componentwise an isomorphism of types: This is
the displayed equivalent of an isomorphism of precategories.

```agda
  Displayed-pathp
    : (eqv : is-precat-iso F)
      → (eqv' : is-precat-iso[ eqv ] G )
    → PathP (λ i → Displayed (Precategory-path F eqv i) o' ℓ') ℰ ℱ
  Displayed-pathp eqv eqv' = displayed-pathp-worker input where
    open is-precat-iso[_] eqv' renaming (has-is-iso' to obeqv ; has-is-ff' to homeqv)
    ps = Precategory-path F eqv
```

We'll define a `displayed-pathp-data`{.Agda}. We define the paths
between displayed object spaces and displayed path spaces by gluing
_against the ungluing_ of the paths in the underlying category, in the
right endpoint category $\cF$. Diagrammatically, this looks something
like

~~~{.quiver}
\[\begin{tikzcd}
  {\mathcal{E}[x]} && {\mathcal{F}[x]} \\
  \\
  {\mathcal{F}[Fx]} && {\mathcal{F}[x]}
  \arrow[""{name=0, anchor=center, inner sep=0}, "{\mathcal{F}(\unglue(\partial i, x))}"', from=3-1, to=3-3]
  \arrow["{F_0'}"', from=1-1, to=3-1]
  \arrow["{\mathrm{id}}", from=1-3, to=3-3]
  \arrow[""{name=1, anchor=center, inner sep=0}, dashed, from=1-1, to=1-3]
  \arrow["{\Glue\ ...}"{description}, draw=none, from=1, to=0]
\end{tikzcd}\]
~~~

```agda
    p1 : PathP (λ i → ps i .Ob → Type o') ℰ.Ob[_] ℱ.Ob[_]
    p1 i x = Glue ℱ.Ob[ unglue x ] λ where
      (i = i0) → ℰ.Ob[ x ] , G.F₀' , obeqv x
      (i = i1) → ℱ.Ob[ x ] , _ , id-equiv
```

We glue the type $\cE[x]$ along $F_0'$ --- the action of the
displayed functor on objects --- against the line of types given by
applying the space of displayed objects of $\cF$ to the ungluing of
$x$, giving a line of type families `p1`{.Agda} ranging from $\cE[-]
\to \cF[-]$. The situation for Hom spaces is analogous.

```agda
    p2 : PathP
      (λ i → {x y : ps i .Ob} (f : ps i .Hom x y) → p1 i x → p1 i y → Type ℓ')
      ℰ.Hom[_] ℱ.Hom[_]
    p2 i {x} {y} f x' y' = Glue (ℱ.Hom[ unglue f ] (unglue x') (unglue y')) λ where
      (i = i0) → ℰ.Hom[ f ] x' y' , G.F₁' , homeqv
      (i = i1) → ℱ.Hom[ f ] x' y' , id≃
```

<!--
```agda
    abstract
      hom[]-coh
        : PathP
          (λ i → (a b : ps i .Ob) (x : p1 i a) (y : p1 i b) (f g : ps i .Hom a b)
                → (f' : p2 i {a} {b} f x y) → f ≡ g → p2 i {a} {b} g x y)
          (λ a b x y f g p f' → ℰ.hom[_] {a} {b} {x} {y} {f} {g} f' p)
          (λ a b x y f g p f' → ℱ.hom[_] {a} {b} {x} {y} {f} {g} f' p)
      hom[]-coh = ua→ λ a → ua→ λ b → ua→ λ x → ua→ λ y → ua→ λ f → ua→ λ g → ua→ λ f' → funext-dep λ {x₀} {x₁} p →
        path→ua-pathp _ (J (λ g x₀ → (x₁ : F.₁ f ≡ F.₁ g) → x₁ ≡ ap F.₁ x₀ → G.F₁' (ℰ.hom[ x₀ ] f') ≡ ℱ.hom[ x₁ ] (G.F₁' f'))
          (λ p r → ap G.F₁' (sym (ℰ.coh[ refl ] f')) ∙ sym (ap₂ ℱ.hom[_] r refl ∙ sym (ℱ.coh[ refl ] _))) x₀ x₁ λ i j → unattach (∂ i) (p (~ i) j))
```
-->

```agda
    open displayed-pathp-data
    input : displayed-pathp-data
    input .obp  = p1
    input .homp = p2
```

We now "just" have to produce inhabitants of `p2`{.Agda} along $i : \II$
which restrict to $\cE$ and $\cF$'s identity morphisms (and
composition morphisms) at the endpoints of $i$. We can do so by gluing,
now at the level of terms, against a heterogeneous composition. The
details are quite nasty, but the core of it is extending the witness
that $G$ respects identity to a path, over line given by gluing
$F_1'$ and ungluing the domain/codomain, between the identity maps in
$\cE$ and $\cF$.

```agda
    input .idp i {x} {x'} = attach (∂ i)
      (λ { (i = i0) → ℰ.id' ; (i = i1) → ℱ.id' })
      (inS (comp (λ j → ℱ.Hom[ p (~ j) ] (unglue x') (unglue x')) (∂ i)
        λ { j (j = i0) → ℱ.id'
          ; j (i = i0) → G.F-id' (~ j)
          ; j (i = i1) → ℱ.id' }))
      where
        p : unglue (ps i .id {x}) ≡ C.id
        p j = hfill (∂ i) (~ j) λ where
          k (k = i0) → C.id
          k (i = i0) → F.F-id (~ k)
          k (i = i1) → C.id
```

<details>
<summary>The case for compositions is analogous and yet much nastier, so
I won't comment on it. You can't make me.</summary>

```agda
    input .compp i {x} {y} {z} {f} {g} {x'} {y'} {z'} f' g' = attach _
      (λ { (i = i0) → f' ℰ.∘' g' ; (i = i1) → f' ℱ.∘' g' })
      (inS (comp (λ j → ℱ.Hom[ p j ] (unglue x') (unglue z')) (∂ i)
        λ { k (k = i0) → unglue f' ℱ.∘' unglue g'
          ; k (i = i0) → G.F-∘' {f' = f'} {g' = g'} (~ k)
          ; k (i = i1) → f' ℱ.∘' g' }))
      where
        p : I → C .Hom (unglue x) (unglue z)
        p j = hfill (∂ i) j λ where
          k (i = i0) → F.F-∘ f g (~ k)
          k (i = i1) → f C.∘ g
          k (k = i0) → unglue f C.∘ unglue g

    input .hom[]p i {a} {b} {x} {y} {f} {g} p f' = hom[]-coh i a b x y f g f' p
```

</details>

<!--
```agda
module
  _ {o ℓ o' ℓ'} {B : Precategory o ℓ} {ℰ ℱ : Displayed B o' ℓ'}
    (F : Displayed-functor Id ℰ ℱ)
  where
  private
    module F = Displayed-functor F
    module ℰ = Displayed ℰ
```
-->

As one last step, we show that if the functor $G$ is displayed over the
identity, the path $\cE \to \cF$ is an actual identity, rather
than a `PathP`{.Agda}.

```agda
  Displayed-path
    : is-precat-iso[ iso id-equiv id-equiv ] F
    → ℰ ≡ ℱ
  Displayed-path eqv' =
    transport
      (λ i → PathP
        (λ j → Displayed
          (to-path-refl {a = B} Precategory-identity-system i j) o' ℓ') ℰ ℱ)
      (Displayed-pathp Id F (iso id-equiv id-equiv) eqv')
```
