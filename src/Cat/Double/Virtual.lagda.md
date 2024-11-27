<!--
```agda
open import Cat.Prelude hiding (∣_∣)
```
-->

```agda
module Cat.Double.Virtual (ℓ : Level) where
```

# Double categories

```agda

open import Cat.Instances.Shape.Cospan using (·←·→·)
open import Cat.Functor.Adjoint.Monad
import Cat.Bi.Instances.T-Spans
open import Cat.Instances.StrictCat
open import 1Lab.Reflection.HLevel
open import Cat.Instances.Graphs
open import 1Lab.HLevel.Universe
open import Cat.Instances.Free
open import Cat.Diagram.Monad
open import Data.Fin.Product using (Πᶠ)
open import Cat.Functor.Base using (Cat[_,_])
open import 1Lab.Reflection
open import 1Lab.Type
open import Cat.Diagram.Monad.Pullback

fc : Monad (Graphs ℓ ℓ)
fc = Adjunction→Monad Free-categories⊣Underlying-graph

private module _ where
  open IsCartesianMonad
  fc-is-cart : IsCartesianMonad fc
  fc-is-cart .pres-pullback x = {! !}
  fc-is-cart .unit-is-equifibered f = ?
  fc-is-cart .mult-is-equifibered f = ?

  fc-cart = cartesian-monad fc fc-is-cart



module fc where
  open CartesianMonad fc-cart public
  open Cat.Bi.Instances.T-Spans fc-cart public


```
