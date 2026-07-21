<!--
```agda
open import Cat.Monoidal.Base
open import Cat.Bi.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Bi.Instances.Delooping where
```

# Deloopings of monoidal categories

Just as a monoid can be [promoted] to a 1-object category, with the
underlying set of the monoid becoming the single $\hom$-set, we can
deloop a [[monoidal category]] into a [[bicategory]] with a single object,
where the sole $\hom$-_category_ is given by the monoidal category.

[promoted]: Cat.Instances.Delooping.html

```agda
Deloop
  : ∀ {o ℓ} {C : Precategory o ℓ} → Monoidal-category C → Prebicategory lzero o ℓ
Deloop {C = C} mon = bi where
  open Prebicategory
  module M = Monoidal-category mon
  bi : Prebicategory _ _ _
  bi .Ob = ⊤
  bi .Hom _ _ = C
  bi .id = M.Unit
  bi .compose = M.-⊗-
  bi .unitor-l = M.unitor-l
  bi .unitor-r = M.unitor-r
  bi .associator = M.associator
  bi .triangle _ _ = M.triangle
  bi .pentagon _ _ _ _ = M.pentagon
```

This makes the idea that a monoidal category is "just" the categorified
version of a monoid precisely, and it's generally called the _delooping
hypothesis_: A monoidal $n$-category is the same as an $(n+1)$-category
with a single object.

We can go the other direction, from bicategories to monoidal categories,
by taking [[endomorphism categories]].
