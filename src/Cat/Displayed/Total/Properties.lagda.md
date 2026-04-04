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

# Total Paths

Opposites of [[displayed categories]] are somewhat subtle, as there are
multiple constructions that one could reasonably call the "opposite".
The most obvious construction is to construct a new displayed category
over $\ca{B}\op$; we call this category the **total opposite** of
$\ca{E}$.

```agda
module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} (ℬ  : Displayed B o' ℓ') (𝒞  : Displayed B o' ℓ') where

  ∫-injblah : ∫ ℬ  ≡ ∫ 𝒞  →  ℬ  ≡ 𝒞

```
