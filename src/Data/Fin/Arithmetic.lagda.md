<!--
```agda
open import 1Lab.Prelude

open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Fin.Base
open import Data.Nat.Base
```
-->

```agda
module Data.Fin.Arithmetic where
```

# Modular arithmetic on finite sets

```agda
_%ᶠ_ : (x n : Nat) ⦃ _ : Positive n ⦄ → Fin n
x %ᶠ n = fin (x % n) ⦃ x%y<y x n ⦄

infixl 8 _%ᶠ_

%ᶠ-pres-0 : ∀ {n} ⦃ _ : Positive n ⦄ → 0 %ᶠ n ≡ 0
%ᶠ-pres-0 {suc _} = refl

module _ {n : Nat} ⦃ n-pos : Positive n ⦄ where
  private
    [_] : Nat → Fin n
    [_] = (_%ᶠ n)

  _+ₘ_ : Fin n → Fin n → Fin n
  x +ₘ y = [ lower x + lower y ]

  _*ₘ_ : Fin n → Fin n → Fin n
  x *ₘ y = [ lower x * lower y ]

  -ₘ_ : Fin n → Fin n
  -ₘ x = [ n - lower x ]

  _-ₘ_ : Fin n → Fin n → Fin n
  x -ₘ y = x +ₘ (-ₘ y)

  1ₘ : Fin n
  1ₘ = 1 %ᶠ n

  infixl 8 _+ₘ_ _-ₘ_
  infixl 9 _*ₘ_
  
  lower-%ᶠ : (x : Fin n) → [ lower x ] ≡ x
  lower-%ᶠ (fin x ⦃ x<b ⦄) = fin-ap $ x<y→x%y≡x x n x<b

  %ᶠ-clear : ∀ x y → [ x * n + y ] ≡ [ y ]
  %ᶠ-clear x y = fin-ap $ (%-clear n x y)

  %ᶠ-ker : ∀ x → [ x * n ] ≡ 0
  %ᶠ-ker x = ap [_] (sym (+-zeror (x * n))) ∙∙ %ᶠ-clear x 0 ∙∙ %ᶠ-pres-0

  %ᶠ-pres-+ : ∀ x y → [ x + y ] ≡ [ x ] +ₘ [ y ]
  %ᶠ-pres-+ x y = fin-ap $ %-pres-+ n x y
  
  %ᶠ-pres-* : ∀ x y → [ x * y ] ≡ [ x ] *ₘ [ y ]
  %ᶠ-pres-* x y = fin-ap $ %-pres-* n x y

  +ₘ-associative : ∀ x y z → x +ₘ (y +ₘ z) ≡ (x +ₘ y) +ₘ z
  +ₘ-associative x y z =
    ⌜ x ⌝ +ₘ (y +ₘ z)                 ≡˘⟨ ap¡ (lower-%ᶠ x) ⟩
    [ lower x ] +ₘ (y +ₘ z)           ≡˘⟨ %ᶠ-pres-+ _ _ ⟩
    [ lower x + (lower y + lower z) ] ≡⟨ ap [_] $ +-associative (lower x) (lower y) (lower z) ⟩
    [ lower x + lower y + lower z ]   ≡⟨ %ᶠ-pres-+ _ _ ⟩
    (x +ₘ y) +ₘ ⌜ [ lower z ] ⌝       ≡⟨ ap! (lower-%ᶠ z) ⟩
    x +ₘ y +ₘ z                       ∎

  +ₘ-zerol : ∀ x → 0 +ₘ x ≡ x
  +ₘ-zerol x = lower-%ᶠ x
  
  +ₘ-zeror : ∀ x → x +ₘ 0 ≡ x
  +ₘ-zeror x =
    x +ₘ 0      ≡⟨ (ap (_%ᶠ n) $ +-zeror (lower x)) ⟩
    [ lower x ] ≡⟨ lower-%ᶠ x ⟩
    x           ∎

  +ₘ-commutative : ∀ x y → x +ₘ y ≡ y +ₘ x
  +ₘ-commutative x y = ap [_] $ +-commutative (lower x) (lower y)

  *ₘ-associative : ∀ x y z → x *ₘ (y *ₘ z) ≡ (x *ₘ y) *ₘ z
  *ₘ-associative x y z =
    ⌜ x ⌝ *ₘ (y *ₘ z)                 ≡˘⟨ ap¡ (lower-%ᶠ x) ⟩
    [ lower x ] *ₘ (y *ₘ z)           ≡˘⟨ %ᶠ-pres-* _ _ ⟩
    [ lower x * (lower y * lower z) ] ≡⟨ (ap [_] $ *-associative (lower x) (lower y) (lower z)) ⟩
    [ lower x * lower y * lower z ]   ≡⟨ %ᶠ-pres-* _ _ ⟩
    x *ₘ y *ₘ ⌜ [ lower z ] ⌝         ≡⟨ ap! (lower-%ᶠ z) ⟩
    x *ₘ y *ₘ z                       ∎

  *ₘ-onel : ∀ x → 1ₘ *ₘ x ≡ x
  *ₘ-onel x =
    1ₘ *ₘ ⌜ x ⌝       ≡˘⟨ ap¡ (lower-%ᶠ x) ⟩
    1ₘ *ₘ [ lower x ] ≡˘⟨ %ᶠ-pres-* _ _ ⟩
    [ 1 * lower x ]   ≡⟨ (ap (_%ᶠ n) $ *-onel (lower x)) ⟩
    [ lower x ]       ≡⟨ lower-%ᶠ x ⟩
    x                 ∎

  *ₘ-oner : ∀ x → x *ₘ 1ₘ ≡ x
  *ₘ-oner x =
    ⌜ x ⌝ *ₘ 1ₘ       ≡˘⟨ ap¡ (lower-%ᶠ x) ⟩
    [ lower x ] *ₘ 1ₘ ≡˘⟨ %ᶠ-pres-* _ _ ⟩
    [ lower x * 1 ]   ≡⟨ ap [_] $ *-oner (lower x) ⟩
    [ lower x ]       ≡⟨ lower-%ᶠ x ⟩
    x                 ∎

  *ₘ-commutative : ∀ x y → x *ₘ y ≡ y *ₘ x
  *ₘ-commutative x y = ap [_] $ *-commutative (lower x) (lower y)

  +ₘ-invr : ∀ x → x -ₘ x ≡ 0
  +ₘ-invr x =
    ⌜ x ⌝ -ₘ x                  ≡˘⟨ ap¡ (lower-%ᶠ x) ⟩
    [ lower x ] -ₘ x            ≡˘⟨ %ᶠ-pres-+ _ _ ⟩
    [ lower x + (n - lower x) ] ≡⟨ ap [_] (monus-+l-inverse (lower x) n (<-weaken (Fin.bounded x))) ⟩
    [ n ]                       ≡⟨ ap [_] (sym (*-onel n)) ∙ %ᶠ-ker 1 ⟩
    0                           ∎

  *ₘ-distrib-+ₘr : ∀ z x y → (x +ₘ y) *ₘ z ≡ x *ₘ z +ₘ y *ₘ z
  *ₘ-distrib-+ₘr z x y =
    (x +ₘ y) *ₘ ⌜ z ⌝                         ≡˘⟨ ap¡ (lower-%ᶠ z) ⟩
    (x +ₘ y) *ₘ [ lower z ]                   ≡˘⟨ %ᶠ-pres-* _ _ ⟩
    [ (lower x + lower y) * (lower z) ]       ≡⟨ ap [_] $ *-distrib-+r (lower x) (lower y) (lower z) ⟩
    [ lower x * lower z + lower y * lower z ] ≡⟨ %ᶠ-pres-+ _ _ ⟩
    x *ₘ z +ₘ y *ₘ z                          ∎

  *ₘ-distrib-+ₘl : ∀ z x y → z *ₘ (x +ₘ y) ≡ z *ₘ x +ₘ z *ₘ y
  *ₘ-distrib-+ₘl z x y =
    ⌜ z ⌝ *ₘ (x +ₘ y)                         ≡˘⟨ ap¡ (lower-%ᶠ z) ⟩
    [ lower z ] *ₘ (x +ₘ y)                   ≡˘⟨ %ᶠ-pres-* _ _ ⟩
    [ (lower z) * (lower x + lower y) ]       ≡⟨ ap [_] $ *-distrib-+l (lower x) (lower y) (lower z) ⟩
    [ lower z * lower x + lower z * lower y ] ≡⟨ %ᶠ-pres-+ _ _ ⟩
    z *ₘ x +ₘ z *ₘ y                          ∎
```
