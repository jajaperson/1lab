<!--
```agda
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

open Displayed
```
-->

```agda
module Cat.Displayed.Instances.Sigma 
  {oa ℓa oe ℓe of ℓf} 
  {𝒜 : Precategory oa ℓa}
  (ℰ : Displayed 𝒜 oe ℓe) (ℱ : Displayed (∫ ℰ) of ℓf)
  where
```

<!--
```agda
private 
  module ℰ = Displayed ℰ
  module ∫ℰ = Precategory (∫ ℰ)
  module ℱ = Displayed ℱ
```
-->

# Sigma displayed category

Let $\cE$ be a [[displayed category]] over $\cA$, and $\cF$ be a
displayed category over the [[total category]] $\int \cE$. The 
**Σ-category** $\sum_{\cE} \cF$ of $\cF$ over $\cA$ is a displayed 
category over $\cA$.

```agda 
Σ[_] : Displayed 𝒜 (oe ⊔ of) (ℓe ⊔ ℓf)
Σ[_] .Ob[_] x = Σ ℰ.Ob[ x ] λ x' → ℱ.Ob[ x , x' ]
Σ[_] .Hom[_] f (x , x') (y , y')  = Σ (ℰ.Hom[ f ] x y) λ f' → ℱ.Hom[ ∫hom f f' ] x' y'

Σ[_] .Hom[_]-set f (x , x') (y , y') = hlevel 2
Σ[_] .id' = ∫ℰ.id .∫Hom.snd , ℱ.id'
Σ[_] ._∘'_ (f' , f'') (g' , g'') = f' ℰ.∘' g' , f'' ℱ.∘' g''
Σ[_] .idr' (f' , f'') = Σ-pathp (ℰ.idr' f') (ℱ.idr' f'')
Σ[_] .idl' (f' , f'') = Σ-pathp (ℰ.idl' f') (ℱ.idl' f'')
Σ[_] .assoc' (f' , f'') (g' , g'') (h' , h'') = Σ-pathp
    (ℰ.assoc' f' g' h') (ℱ.assoc' f'' g'' h'')
Σ[_] .hom[_] p (f' , f'') = ℰ.hom[ p ] f'
  , ℱ.hom[ ∫Hom-path ℰ p (ℰ.coh[ p ] f') ] f''
Σ[_] .coh[_] p (f' , f'') = Σ-pathp (ℰ.coh[ p ] f') 
  (ℱ.coh[ (λ i → ∫hom (p i) (ℰ.coh[ p ] f' i)) ] f'')
```
