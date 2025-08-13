<!--
```agda
open import Algebra.Ring.Ideal
open import Algebra.Group.Subgroup
open import Algebra.Ring.Module
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Displayed.Total
open import Cat.Prelude

open import Data.Power

import Algebra.Ring.Reasoning as Ringr
```
-->

```agda
module Algebra.Ring.Ideal.Properties where
```

# Ideals in rings
<!--
```agda
module _ {ℓ} {Q R : Ring ℓ} {S : ℙ ⌞ R ⌟} (I : is-ideal R S) (f : Rings.Hom Q R) where
  private
    module f = RingHom f
    module I = is-ideal I
```
-->

```agda
  open is-ideal
  inverse-is-ideal : is-ideal Q (S ⊙ apply f)
  inverse-is-ideal .has-rep-subgroup = inverse-represents-subgroup I.has-rep-subgroup f.ring-hom→group-hom
  inverse-is-ideal .has-*ₗ x {y} p = subst (_∈ S) (sym (f.pres-* _ _)) $ I.has-*ₗ (f · x) {f · y} p
  inverse-is-ideal .has-*ᵣ x {y} p = subst (_∈ S) (sym (f.pres-* _ _)) $ I.has-*ᵣ (f · x) {f · y} p
```
# Kernels


<!--
```agda
module _ {ℓ} {Q R : Ring ℓ} (f : Rings.Hom Q R) where
  private
    module f = RingHom f
    open module R = Ringr R
    module Q = Ringr Q
  open Ideal
  open is-ideal
```
-->
```agda
  Kernel : Ideal Q
  Kernel .𝔞 x = elΩ (f · x ≡ 0r)
  Kernel .has-is-ideal .has-rep-subgroup = kernel-represents-subgroup f.RingHom→GroupHom
  Kernel .has-is-ideal .has-*ₗ x {y} = rec! λ p → inc (
    f · (x Q.* y)   ≡⟨ f.pres-* _ _ ⟩
    f · x R.* f · y ≡⟨ *absorbr p ⟩
    0r ∎)
  Kernel .has-is-ideal .has-*ᵣ x {y} = rec! λ p → inc (
    f · (y Q.* x)   ≡⟨ f.pres-* _ _ ⟩
    f · y R.* f · x ≡⟨ *absorbl p ⟩
    0r ∎)


```
