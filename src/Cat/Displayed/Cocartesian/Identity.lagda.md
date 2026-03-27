<!--
```agda
open import Cat.Displayed.Cartesian.Identity
open import Cat.Displayed.Base
open import Cat.Prelude
open import Cat.Displayed.Total.Op
open import Cat.Displayed.Univalence.Op

import Cat.Displayed.Cocartesian as Cocar
import Cat.Displayed.Univalence.Reasoning
import Cat.Displayed.Univalence
import Cat.Displayed.Reasoning as Dr
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Cocartesian.Identity
  {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ')
  where
```

# Identity of cocartesian lifts

<!--
```agda
private
  module B = Cr B

open Cocar E
open Cat.Displayed.Univalence.Reasoning E
open Cat.Displayed.Univalence E
open Dr E

module _ {a b a'} (e-cat : is-category-displayed) (f : B.Hom a b) where
```
-->

In this module, we prove that [[CoCartesian lifts]] in a [[displayed
univalent category]] form a [[proposition]].

```agda
  Cocartesian-lift-is-prop : is-prop (Cocartesian-lift f a')
  Cocartesian-lift-is-prop = Equiv→is-hlevel 1 cocartesian-lift≃co-cartesian-lift $
    Cartesian-lift-is-prop (E ^total-op) (total-op-is-category E e-cat) f


  Cartesian-morphism-is-prop : ∀ {b'} → is-prop (Cocartesian-morphism f a' b')
  Cartesian-morphism-is-prop = ?
```
