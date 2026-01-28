<!--
```agda
open import Cat.Bi.Base
open import Cat.Prelude
open import Cat.Bi.Diagram.Adjunction
open import Cat.Bi.AdjointEquiv
```
-->

```agda
module Cat.Bi.Univalent where
```

<!--
```agda
open _=>_

open Prebicategory
--module _ {o ℓ ℓ'} (B : Prebicategory o ℓ ℓ') where
--  private module B = Prebicategory B

private variable
  o ℓ ℓ' : Level
```
-->

# Univalent bicategories

```agda


is-local-bicategory : (B : Prebicategory o ℓ ℓ') → Type (o ⊔ ℓ ⊔ ℓ')
is-local-bicategory B = ∀ a b → is-category $ B .Hom a b

is-global-bicategory : (B : Prebicategory o ℓ ℓ') → Type (o ⊔ ℓ ⊔ ℓ')
is-global-bicategory B = is-identity-system (adjoint-equivalence B) {! !}

record is-bicategory (B : Prebicategory o ℓ ℓ') : Type (o ⊔ ℓ ⊔ ℓ') where
  field

```
