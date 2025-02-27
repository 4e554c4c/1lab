<!--
```agda
open import Cat.Functor.Properties
open import Cat.Diagram.Pullback
open import Cat.Functor.Pullback as P hiding (pres-pullback)
--open import Cat.Diagram.Initial
--open import Cat.Functor.Adjoint
--open import Cat.Functor.Compose
--open import Cat.Instances.Comma
--open import Cat.Instances.Slice
open import Cat.Diagram.Monad
open import Cat.Prelude
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
      unit-is-equifibered : is-equifibred T.unit
      mult-is-equifibered : is-equifibred T.mult


module _ (C : Precategory o ℓ) where
  record CartesianMonad : Type (o ⊔ ℓ) where
    constructor cartesian-monad
    field
      U : Monad C
      is-cartesian : IsCartesianMonad U
    open Monad U public
    open IsCartesianMonad is-cartesian public

```
