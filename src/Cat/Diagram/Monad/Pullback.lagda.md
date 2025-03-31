<!--
```agda
open import Cat.Functor.Properties
open import Cat.Diagram.Pullback
open import Cat.Functor.Pullback as P hiding (pres-pullback)
--open import Cat.Diagram.Initial
--open import Cat.Functor.Adjoint
open import Cat.Functor.Reasoning
--open import Cat.Instances.Comma
--open import Cat.Instances.Slice
open import Cat.Diagram.Monad
open import Cat.Prelude

import Cat.Diagram.Monad.Reasoning
```
-->
```agda


module Cat.Diagram.Monad.Pullback {o ℓ} where

module _ {C : Precategory o ℓ} where
  private module C = Precategory C

  record IsCartesianMonad (T : Monad C) : Type (o ⊔ ℓ) where
    private
      module T = Monad T

    field
      pres-pullback : P.pres-pullback T.M
      unit-is-equifibred : is-equifibred T.unit
      mult-is-equifibred : is-equifibred T.mult


record CartesianMonad (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  constructor cartesian-monad
  field
    U : Monad C
    is-cartesian : IsCartesianMonad U
  open Cat.Diagram.Monad.Reasoning U public
  open IsCartesianMonad is-cartesian public
```
