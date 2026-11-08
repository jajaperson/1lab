<!--
```agda
open import Algebra.Group.Cat.Isofibration
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Displayed.Isofibration
open import Cat.Instances.Sets
open import Cat.Prelude

import Cat.Displayed.Morphism as Dm
import Cat.Morphism as Cm
```
-->

```agda
module Algebra.Group.Ab.Cat.Isofibration (ℓ : Level) where
```

<!--
```agda
open Isofibration (Groups-isofibration ℓ)
private
  module Sets = Cm (Sets ℓ)
  module Grp = Dm (Groups-on ℓ)
open Dm (Abelian-groups-on ℓ)
```
-->

# The abelian groups isofibration {defines="abelian-groups-isofibration"}

This module repackages the [[groups isofibration]] into one for
[[abelian groups]].

```agda
private module _ {A B} (e≅ : A Sets.≅ B) (Aᵃ : Abelian-group-on ⌞ A ⌟) where
  open Equiv (iso→equiv e≅)
  module A = Abelian-group-on Aᵃ

  Aᵍ : Group-on ⌞ A ⌟
  Aᵍ = Abelian→Group-on Aᵃ

  Bᵍ : Group-on ⌞ B ⌟
  Bᵍ = e≅ ^* Aᵍ
  module B = Group-on Bᵍ

  Aᵍ≅Bᵍ : Aᵍ Grp.≅[ e≅ ] Bᵍ
  Aᵍ≅Bᵍ = ^*-lifts e≅ Aᵍ
  
  B-commutes : ∀ {x y} → x B.⋆ y ≡ y B.⋆ x
  B-commutes = ap to A.commutes

  Bᵃ : Abelian-group-on ⌞ B ⌟
  Bᵃ = record
    { _*_ = B._⋆_ ; has-is-ab = record
      { has-is-group = B.has-is-group ; commutes = B-commutes }
    }

  Aᵃ≅Bᵃ :  Aᵃ ≅[ e≅ ] Bᵃ 
  Aᵃ≅Bᵃ = record
    { to' = Grp.to' Aᵍ≅Bᵍ ; from' = Grp.from' Aᵍ≅Bᵍ
    ; inverses' = record { invl' = prop! ; invr' = prop! }
    }

Ab-isofibration : Isofibration (Abelian-groups-on ℓ)
Ab-isofibration = record { _^*_ = Bᵃ ; ^*-lifts = Aᵃ≅Bᵃ }
```
