<!--
```agda
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring
open import Algebra.Ring.Ideal
open import Algebra.Ring.Ideal.Properties

open import Algebra.Ring.Quotient

open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude hiding (_+_ ; _*_; _-_)
open import Cat.Regular
open import Cat.Morphism.Factorisation

open import Data.Int.Properties
open import Data.Int.Base

import Algebra.Ring.Reasoning as Kit

import Cat.Displayed.Instances.Subobjects
import Data.Nat as Nat
import Prim.Data.Nat as Nat
import Algebra.Ring.Reasoning as Ringr
```
-->

```agda
module Algebra.Ring.Cat.Regular {ℓ} where
```

<!--
```agda
open Cat.Displayed.Instances.Subobjects (Rings ℓ)
open is-regular
open Factorisation
```
-->

```agda

Subring : Ring ℓ → Type (lsuc ℓ)
Subring R = Subobject R

module _ {Q R : Ring ℓ} (f : Rings.Hom Q R) where
  private
    module f = RingHom f
    open module R = Ringr R
    module Q = Ringr Q
  open Ideal
  open is-ideal
  open is-ring-hom
  open Subobject
  im[_]ʳ : Subring R
  im[_]ʳ .domain = Q /ᴿ Kernel f
  im[_]ʳ .map .fst = Quot-elim (λ _ → has-is-set) (apply f) λ x y → elim! λ r →
    f · x                       ≡˘⟨ +-idr ⟩
    f · x + 0r                  ≡˘⟨ +pullr +-invl ⟩
    f · x + (- f · y) + f · y   ≡˘⟨ refl⟩+⟨ f.pres-neg ⟩+⟨refl ⟩
    f · x + f · (Q.- y) + f · y ≡˘⟨ f.pres-+ x (Q.- y) ⟩+⟨refl ⟩
    f · (x Q.-  y) + f · y      ≡⟨ +elimr r ⟩
    f · y                       ∎
  im[_]ʳ .map .snd .pres-id = f.pres-id
  im[_]ʳ .map .snd .pres-+ = elim! λ x y → f.pres-+ x y
  im[_]ʳ .map .snd .pres-* = elim! λ x y → f.pres-* x y
  im[_]ʳ .monic = ext λ g h x → {! unext p $ x  !}

goal : is-regular (Rings ℓ)
goal .factor {Q} {R} f = record where
  mediating = Q /ᴿ Kernel f
  mediate   = inclᴿ Q (Kernel f)
  forget    = {! !}

  mediate∈E = {! !}

  forget∈M  = {! !}
  factors   = {! !}
goal .stable = {! !}
goal .has-is-lex = {! !}

```
