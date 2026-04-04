<!--
```agda
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Equivalence
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Displayed.Univalence
open import Cat.Displayed.Univalence.Reasoning
open import Cat.Displayed.Univalence
open import Cat.Displayed.Univalence.Reasoning
open import Cat.Displayed.Total.Op
open import Cat.Prelude

import Cat.Morphism.Duality as MD
import Cat.Morphism as M
import Cat.Displayed.Morphism as DM
import Cat.Displayed.Morphism.Duality as DMD
import Cat.Displayed.Reasoning as DR
```
-->

```agda
module Cat.Displayed.Univalence.Op
  {o ℓ o' ℓ'} {B : Precategory o ℓ} (ℰ : Displayed B o' ℓ') where

open Functor
open ∫Hom
private
  module B =  M B
  module Bo =  M (B ^op)
  module ℰo = DM (ℰ ^total-op)
  module ℰ = DM ℰ
open MD B
open DMD ℰ
```


# Univalence

```agda
module _ (e-cat : is-category-displayed ℰ) where
  total-op-is-category : is-category-displayed (ℰ ^total-op)
  total-op-is-category f a (b , iso-b) (c , iso-c) = Σ-pathp (ap fst co) $ ℰo.≅[]-pathp λ i → co i .snd .ℰ.from'
    where
    co = e-cat (co-iso→iso $ f Bo.Iso⁻¹) a (b , (co-iso[]→iso[] $ iso-b ℰo.Iso[]⁻¹)) (c , (co-iso[]→iso[] $ iso-c ℰo.Iso[]⁻¹))
```
