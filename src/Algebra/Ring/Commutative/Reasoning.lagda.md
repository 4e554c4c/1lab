<!--
```agda
open import Algebra.Ring.Module.Action
open import Algebra.Ring.Commutative
open import Algebra.Group.Subgroup
open import Algebra.Ring.Module
open import Algebra.Ring.Ideal
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Displayed.Total
open import Cat.Prelude hiding (_*_)

open import Data.Power

import Algebra.Ring.Reasoning as Ringr
```
-->

```agda
module Algebra.Ring.Commutative.Reasoning {ℓ} (R : CRing ℓ) where

open module R = CRing R public


central : ∀ {a} x → a * x ≡ x * a
central _ = *-commutes
```

