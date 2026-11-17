<!--
```agda
open import Cat.Displayed.Multi.Base
open import Cat.Instances.Dist
open import Cat.Morphism.Factorisation
open import Cat.Morphism.Factorisation.Orthogonal
open import Cat.Functor.WideSubcategory
open import Cat.Prelude

import Cat.Displayed.Instances.Identity as Id
import Cat.Displayed.Instances.WideSubcategory as W
```
-->

```agda
module Cat.Displayed.Multi.Instances.Trivial where
```

```agda
open Multicat hiding (Cocartesian-morphism)
open Multicat-over
open Id Dist
TrivialM : Multicat lzero lzero
TrivialM .disp =  IdD
TrivialM .lift-inert f _ tt = IdD-opfibration f tt  
TrivialM .is-multi .idx-is-eqv .is-eqv v = hlevel 0
TrivialM .is-multi .↑ C[_] = tt
TrivialM .is-multi .cocart-proj C[_] k = record where
  hom' = tt
  cocartesian = idd-is-cocartesian 


module dist-ofs = is-ofs inert-active-is-ofs
open W Dist dist-ofs.L-subcat

TrivialM' : Multicat lzero lzero
TrivialM' .disp =  Wide-disp
TrivialM' .lift-inert f p tt = record where
  lifting = p
  cocartesian = {!!} 
TrivialM' .is-multi .idx-is-eqv = {!!}
TrivialM' .is-multi .↑ C[_] = {!!}
TrivialM' .is-multi .cocart-proj C[_] k = record where
  hom' = {!!}
  cocartesian = {!!}
```
