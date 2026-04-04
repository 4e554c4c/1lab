<!--
```agda
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Reasoning as Cr
import Cat.Bi.Diagram.Adjunction as Adj
import Cat.Bi.Reasoning as BR
```
-->

```agda
module Cat.Bi.AdjointEquiv {o ℓ ℓ'} (B : Prebicategory o ℓ ℓ') where
```

<!--
```agda
open Adj B
private
  open module B = BR B
open Hom hiding (id ; to ; from)
open Cr._≅_
```
-->

# Adjoint equivalences

```agda
record is-equivalence {a b} (To : a ↦ b) : Type (o ⊔ ℓ ⊔ ℓ') where


  field
    From : b ↦ a
    adjoint : To ⊣ From
  open _⊣_ adjoint public

  field
    unit-iso   : Cr.is-invertible (Hom a a) η
    counit-iso : Cr.is-invertible (Hom b b) ε

unquoteDecl is-equivalence-path = declare-record-path is-equivalence-path (quote is-equivalence)

record adjoint-equivalence (a b : Ob) : Type (o ⊔ ℓ ⊔ ℓ') where
  field
    To : a ↦ b
    is-adj-equiv : is-equivalence To
  open is-equivalence is-adj-equiv public

unquoteDecl adjoint-equiv-path = declare-record-path adjoint-equiv-path (quote adjoint-equivalence)

open adjoint-equivalence
open _⊣_
open is-equivalence
id-eqv : ∀ a → adjoint-equivalence a a
id-eqv a .To = id
id-eqv a .is-adj-equiv .From = id
id-eqv a .is-adj-equiv .adjoint .η = λ→ id
id-eqv a .is-adj-equiv .adjoint .ε = λ← id
id-eqv _ .is-adj-equiv .adjoint .zig = sym $
  λ← id ∘ λ← id ◀ id ∘ α← ( id , id , id) ∘ id ▶ λ→ id ∘ ρ→ id
  ≡⟨ refl⟩∘⟨ refl⟩∘⟨ pulll triangle-inv ⟩
  λ← id ∘ λ← id ◀ id ∘ ρ→ id ◀ id ∘ ρ→ id
  ≡⟨ λ←≡ρ← ⟩∘⟨ ap (_◀ id) λ←≡ρ← ⟩∘⟨refl ⟩
  ρ← id ∘ ρ← id ◀ id ∘ ρ→ id ◀ id ∘ ρ→ id
  ≡⟨ refl⟩∘⟨ cancell (◀.F-map-iso ρ≅ .invr) ⟩
  ρ← id ∘ ρ→ id
  ≡⟨ ρ≅ .invr ⟩
  Hom.id ∎
id-eqv _ .is-adj-equiv .adjoint .zag = sym $
  ρ← id ∘ id ▶ λ← id ∘ α→ (id , id , id) ∘ λ→ id ◀ id ∘ λ→ id
  ≡⟨ refl⟩∘⟨ pulll triangle-α→ ⟩
  ρ← id ∘ ρ← id ◀ id ∘ λ→ id ◀ id ∘ λ→ id
  ≡˘⟨ λ←≡ρ← ⟩∘⟨ ap (_◀ id) λ←≡ρ← ⟩∘⟨refl ⟩
  λ← id ∘ λ← id ◀ id ∘ λ→ id ◀ id ∘ λ→ id
  ≡⟨ refl⟩∘⟨ cancell (◀.F-map-iso λ≅ .invr) ⟩
  λ← id ∘ λ→ id
  ≡⟨ λ≅ .invr ⟩
  Hom.id ∎
id-eqv a .is-adj-equiv .unit-iso = inverses→invertible $ λ≅ {f = id} .inverses
id-eqv a .is-adj-equiv .counit-iso = inverses→invertible $ (λ≅ {f = id} Hom.Iso⁻¹) .inverses
```
