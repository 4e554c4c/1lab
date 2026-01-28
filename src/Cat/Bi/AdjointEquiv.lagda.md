<!--
```agda
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Reasoning as Cr
import Cat.Bi.Diagram.Adjunction as Adj
```
-->

```agda
module Cat.Bi.AdjointEquiv {o ℓ ℓ'} (B : Prebicategory o ℓ ℓ') where
```

<!--
```agda
open Adj B
private
  open module B = Prebicategory B
```
-->

# Adjoint equivalences

```agda
record is-equivalence {a b} (f : a ↦ b) (g : b ↦ a) (adj : f ⊣ g) : Type (o ⊔ ℓ ⊔ ℓ') where

  open _⊣_ adj public

  field
    unit-iso   : Cr.is-invertible (Hom a a) η
    counit-iso : Cr.is-invertible (Hom b b) ε

record adjoint-equivalence (a b : Ob) : Type (o ⊔ ℓ ⊔ ℓ') where
  field
    f : a ↦ b
    g : b ↦ a
    adj : f ⊣ g
    is-adj-equiv : is-equivalence f g adj

open adjoint-equivalence
open _⊣_
open is-equivalence
id-eqv : ∀ a → adjoint-equivalence a a
id-eqv a .f = id
id-eqv a .g = id
id-eqv a .adj .η = λ→ id
id-eqv a .adj .ε = λ← id
id-eqv a .adj .zig =
  Hom.id ≡⟨ ? ⟩
  λ← id ∘ λ← id ◀ id ∘ α← id id id ∘ id ▶ λ→ id ∘ ρ→ id ∎

id-eqv a .adj .zag =
  Hom.id {a} ≡⟨ ? ⟩
  ρ← id ∘ id ▶ λ← id ∘ α→ id id id ∘ λ→ id ◀ id ∘ λ→ id ∎
id-eqv a .is-adj-equiv .unit-iso = {! !}
id-eqv a .is-adj-equiv .counit-iso = {! !}
```
