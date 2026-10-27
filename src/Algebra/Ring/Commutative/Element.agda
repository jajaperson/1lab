-- Helper module for working with elements of commutative rings

open import Algebra.Ring.Commutative

import Algebra.Ring.Element

module Algebra.Ring.Commutative.Element {ℓ} (R : CRing ℓ) where

open CRing R

private module Re = Algebra.Ring.Element ring

open Re.Commutative *-commutes public

open Re hiding (module Commutative) public
