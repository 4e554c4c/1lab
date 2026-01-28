<!--
```agda
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Fibre.Reasoning
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  where
```

<!--
```agda
private
  open Cat.Displayed.Reasoning E
  open Cat.Displayed.Morphism E
  module B = Cat.Reasoning B
  module Fib {x} = Cat.Reasoning (Fibre E x)

open Fib public
```
-->


## Reasoning in fibre categories

This module defines some helpers to help formalisation go smoother when
we're working with fibre categories. Mathematically, it's not very
interesting: it's pure engineering.

```agda
private variable
  a b c d x y z : B.Ob
  x' x'' y' z' z'' : Ob[ x ]
  a' b' c' d' : Ob[ a ]
  f g h i j k : B.Hom x y
  f' g' h' i' j' k' : Hom[ f ] x' y'
  p : f ≡ g

opaque
  to-fibre : f' ∘' g' ≡[ B.idl _ ] f' Fib.∘ g'
  to-fibre = to-pathp[] refl

  over-fibre
    : f' ∘' g' ≡[ p ] h' ∘' i'
    → f' Fib.∘ g' ≡ h' Fib.∘ i'
  over-fibre p' = ap hom[] (cast[] p')

module _ (o : x' ≅↓ y') where
  open module o = _≅[_]_ o
  open Inverses
  iso→isof : x' Fib.≅ y'
  iso→isof .to = o.to'
  iso→isof .from = o.from'
  iso→isof .inverses .invl = from-pathp[] o.invl'
  iso→isof .inverses .invr = from-pathp[] o.invr'

opaque
  pullrf
    : g' ∘' h' ≡[ p ] i'
    → (f' Fib.∘ g') ∘' h' ≡[ p ∙ sym (B.idl _) ] f' ∘' i'
  pullrf p' = cast[] $ to-pathp[]⁻ (whisker-l (B.idl _)) ∙[] pullr[] _ p'

opaque
  pulllf
    : f' ∘' g' ≡[ p ] i'
    → f' ∘' (g' Fib.∘ h') ≡[ p ∙ sym (B.idr _) ] i' ∘' h'
  pulllf p' = cast[] $ to-pathp[]⁻ (whisker-r (B.idl _)) ∙[] pulll[] _ p'

opaque
  pushrf
    : {p : i ≡ B.id B.∘ h}
    → i' ≡[ p ] g' ∘' h'
    → f' ∘' i' ≡[ B.idl _ ∙ p ] (f' Fib.∘ g') ∘' h'
  pushrf {h = h} p' =
    cast[] $ pushr[] _ p'
    ∙[] to-pathp[] (unwhisker-l (ap (B._∘ h) (B.idl _)) (B.idl _))

opaque
  pushlf
    : {p : i ≡ f B.∘ B.id}
    → i' ≡[ p ] f' ∘' g'
    → i' ∘' h' ≡[ B.idr _ ∙ p ] f' ∘' (g' Fib.∘ h')
  pushlf {f = f} p' =
    cast[] $ pushl[] _ p'
    ∙[] to-pathp[] (unwhisker-r (ap (f B.∘_) (B.idl _)) (B.idl _))

opaque
  extendrf
    : {p : B.id B.∘ i ≡ B.id B.∘ k}
    → g' ∘' i' ≡[ p ] h' ∘' k'
    → (f' Fib.∘ g') ∘' i' ≡[ p ] (f' Fib.∘ h') ∘' k'
  extendrf {k = k} p' = cast[] $
    to-pathp[]⁻ (whisker-l (B.idl _))
    ∙[] extendr[] _ p'
    ∙[] to-pathp[] (unwhisker-l (ap (B._∘ k) (B.idl _)) (B.idl _))

opaque
  extendlf
    : {p : f B.∘ B.id ≡ g B.∘ B.id}
    → f' ∘' h' ≡[ p ] g' ∘' k'
    → f' ∘' (h' Fib.∘ i') ≡[ p ] g' ∘' (k' Fib.∘ i')
  extendlf {g = g} p' = cast[] $
    to-pathp[]⁻ (whisker-r (B.idl _))
    ∙[] extendl[] _ p'
    ∙[] to-pathp[] (unwhisker-r (ap (g B.∘_) (B.idl _)) (B.idl _))

opaque
  cancellf
    : {p : f B.∘ B.id ≡ B.id}
    → f' ∘' g' ≡[ p ] id'
    → f' ∘' (g' Fib.∘ h') ≡[ p ] h'
  cancellf p' = cast[] $ to-pathp[]⁻ (whisker-r (B.idl _)) ∙[] cancell[] _ p'

opaque
  cancelrf
    : {p : B.id B.∘ h ≡ B.id}
    → g' ∘' h' ≡[ p ] id'
    → (f' Fib.∘ g') ∘' h' ≡[ p ] f'
  cancelrf p' = cast[] $ to-pathp[]⁻ (whisker-l (B.idl _)) ∙[] cancelr[] _ p'
```
