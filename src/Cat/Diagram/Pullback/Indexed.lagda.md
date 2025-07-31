<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Univalent
open import Cat.Prelude
open import Cat.Instances.Slice
open import Cat.Diagram.Product.Indexed

open import 1Lab.Prelude
```
-->

```agda
module Cat.Diagram.Pullback.Indexed {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
import Cat.Reasoning C as C
private variable
  o' ℓ' : Level
  Idx : Type ℓ'
  A B P : C.Ob
```
-->

# Wide pullabacks {defines="wide-pullback indexed-pullback"}

```agda
is-ｐｕｌｌｂａｃｋ : {c : C.Ob} (F : Idx → /-Obj c) (π : ∀ i → /-Hom (cut C.id) (F i)) → Type (o ⊔ ℓ ⊔ level-of Idx)
is-ｐｕｌｌｂａｃｋ {c = c} = is-indexed-product (Slice C c)

Ｐｕｌｌｂａｃｋ : {c : C.Ob} (F : Idx → /-Obj c) → Type (o ⊔ ℓ ⊔ level-of Idx)
Ｐｕｌｌｂａｃｋ {c = c} = Indexed-product (Slice C c)
```

The empty wide pullback is merely the identity morphism
```agda
id-is-ｐｕｌｌｂａｃｋ : ∀ {c} → is-ｐｕｌｌｂａｃｋ {Idx = ⊤} {c = c}  (λ _ → cut C.id) λ { _ → {! !} } 
```
