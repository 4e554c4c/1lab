<!--
```agda
open import 1Lab.Prelude hiding (_*_)

open import Algebra.Group
open import Algebra.Group.Cat.Base
open import Algebra.Group.Notation
```
-->

```agda
module Algebra.Group.Reasoning {ℓ} (G : Group ℓ) where
```

# Reasoning combinators for groups

<!--
```agda
--open Group-on (M .snd) renaming (_⋆_ to _*_ ; identity to 1m)
open Multiplicative-notation (G .snd) public
private variable
  a b c d e f f' g g' h h' i w x y z : ⌞ G ⌟
```
-->
```agda

module _ (p : x ≡ 1g) where
  inv-elim : x ⁻¹ ≡ 1g
  inv-elim = ap _⁻¹ p ∙ inv-1
```
