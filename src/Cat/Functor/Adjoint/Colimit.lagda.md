<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Functor.Naturality
open import Cat.Diagram.Initial
open import Cat.Functor.Compose
open import Cat.Instances.Comma
open import Cat.Functor.Base
open import Cat.Functor.Adjoint
open import Cat.Functor.Properties

open import Cat.Diagram.Colimit.Base
open import Cat.Prelude hiding (J)

import Cat.Functor.Reasoning as Func
import Cat.Natural.Reasoning
import Cat.Reasoning
```
-->

<!--
```agda
```
-->
### Free objects and colimits


```agda
module Cat.Functor.Adjoint.Colimit where
private variable
  o ℓ : Level
  C D J : Precategory o ℓ
module _ (U : Functor C D) (is-ff : is-fully-faithful U) {diagram : Functor J C} (colim : Colimit {C = D} (U F∘ diagram)) where
  open Colimit colim
  open Free-object
  colimit→free-object : Colimit diagram → Free-object U coapex
  colimit→free-object = {! !}

  free-object→make-is-colimit : (ob : Free-object U coapex) → make-is-colimit diagram (ob .free)
  free-object→make-is-colimit = {! !}

  free-object→is-colimit : Free-object U coapex → Colimit diagram
  free-object→is-colimit = to-colimit ⊙ to-is-colimit ⊙ free-object→make-is-colimit

```

