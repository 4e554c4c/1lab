<!--
```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Cartesian
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.IsoFibration
  {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') where

open Cat.Displayed.Morphism E
open Cat.Displayed.Cartesian E
open Cat.Reasoning B
open DR E
```

# Isofibrations

```agda
record Iso-lift {x y} (f : x ≅ y) (y' : Ob[ y ]) : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
  field
    {x'}      : Ob[ x ]
    lifting   : x' ≅[ f ] y'
    cartesian : is-cartesian (f .to) (lifting .to')
  open is-cartesian cartesian public

Isofibration : Type _
Isofibration = ∀ {x y} (f : x ≅ y) (y' : Ob[ y ]) → Iso-lift f y'
```
