<!--
```agda
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Product
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Displayed.Base
open import Cat.Displayed.BeckChevalley
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Fibre
open import Cat.Instances.Product
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Reasoning

open import Order.Base
open import Order.Cat
import Order.Reasoning
```
-->

```agda
module Cat.Displayed.Double {o ℓ ℓv ℓ□} where
```

<!--
```agda
```
-->

# double cats

```agda
record DoubleCategoryStructure {C : Precategory o ℓ} (E : Displayed (C ×ᶜ C) ℓv ℓ□) : Type (lsuc (o ⊔ ℓ ⊔ ℓv ⊔ ℓ□)) where
  open module C = Cat.Reasoning C public
  open Cat.Displayed.Reasoning E public
  open Cat.Displayed.Morphism E
  VHom : Ob → Ob → Type ℓv
  VHom a b = Ob[ a , b ]
  Sq : ∀ {x x' y y'} (u : VHom x y) (f : Hom x x') (g : Hom y y') (v : VHom x' y') → Type ℓ□
  Sq u f g v = Hom[ f , g ] u v
  field
    e : ∀ {x} → VHom x x
    id[_] : ∀ {x y} (h : Hom x y) → Sq e h h e

  field
    id[]≡id : ∀ {x} → id[ id {x} ] ≡ id' {x , x}
    id[]∘ : ∀ {x y z} {v : Hom y z} {h : Hom x y} → id[ v ∘ h ] ≡ id[ v ] ∘' id[ h ]

  -- horizontal composition (fails in vdbl?)
  field
    _⊚_ : ∀ {x y z} → (k : VHom y z) (v : VHom x y) → VHom x z
    _⊡_ : ∀ {a b c d e f v₁ v₂ v₃}
      {h₁ : VHom b c} {h₂ : VHom a b}
      {k₁ : VHom e f} {k₂ : VHom d e} →
      (s₁ : Sq h₁ v₂ v₃ k₁) (s₂ : Sq h₂ v₁ v₂ k₂) →
      Sq (h₁ ⊚ h₂) v₁ v₃ (k₁ ⊚ k₂)
```
