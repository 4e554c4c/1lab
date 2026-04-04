<!--
```agda
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Equivalence
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as DR
```
-->

```agda
module Cat.Displayed.Total.Properties where

open Functor
open ∫Hom
```

```agda
module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} (ℬ  : Displayed B o' ℓ') (𝒞  : Displayed B o' ℓ') where

  --∫-inj? : ∫ ℬ  ≡ ∫ 𝒞  →  ℬ  ≡ 𝒞

```
