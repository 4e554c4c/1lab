<!--
```agda
open import Cat.Displayed.Cartesian.Joint
open import Cat.Functor.Equivalence.Path
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Product.Indexed
open import Cat.Displayed.Bifibration
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Functor.Equivalence
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Functor.WideSubcategory
open import Cat.Prelude
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism
import Cat.Reasoning

import Cat.Displayed.Morphism
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Instances.WideSubcategory
  {o ℓ ℓp} (C : Precategory o ℓ) (ｓｕｂｃａｔｅｇｏｒｙ : Wide-subcat C ℓp)
  where
```

```agda
open Wide-subcat ｓｕｂｃａｔｅｇｏｒｙ 
open Cat.Reasoning C

Wide-disp : Displayed C lzero ℓp
Wide-disp = with-thin-display record where
  Ob[_] _ = ⊤
  Hom[_] {x} {y} f _ _ = P f
  id' =  P-id
  _∘'_ = P-∘ 

open DR Wide-disp
```
