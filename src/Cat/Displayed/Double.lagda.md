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

# doubled cats

```agda
record DoubleCategory {C : Precategory o ℓ} (E : Displayed (C ×ᶜ C) ℓv ℓ□) : Type (lsuc (o ⊔ ℓ ⊔ ℓv ⊔ ℓ□)) where
  open module C = Cat.Reasoning C public
  module C² = Cat.Reasoning (C ×ᶜ C)
  open Cat.Displayed.Reasoning E public
  open Cat.Displayed.Morphism E
  --VHom : Ob → Ob → Type ℓv
  --VHom a b = Ob[ a , b ]
  --Sq : ∀ {x x' y y'} (u : VHom x y) (f : Hom x x') (g : Hom y y') (v : VHom x' y') → Type ℓ□
  --Sq u f g v = Hom[ f , g ] u v
  field
    e : ∀ {x} → Ob[ x , x ]
    id[_] : ∀ {x y} (h : Hom x y) → Hom[ h , h ] e e

  field
    id[]≡id : ∀ {x} → id[ id {x} ] ≡ id' {x , x}
    id[]∘ : ∀ {x y z} {v : Hom y z} {h : Hom x y} → id[ v ∘ h ] ≡ id[ v ] ∘' id[ h ]

  -- horizontal composition
  field
    _⊚_ : ∀ {x y z} → (k : Ob[ y , z ]) (v : Ob[ x , y ]) → Ob[ x , z ]
    _⊡_ : ∀ {a b c d e f v₁ v₂ v₃}
      {h₁ : Ob[ b , c ]} {h₂ : Ob[ a , b ]}
      {k₁ : Ob[ e , f ]} {k₂ : Ob[ d , e ]} →
      (s₁ : Hom[ v₂ , v₃ ] h₁ k₁) (s₂ : Hom[ v₁ , v₂ ] h₂ k₂) →
      Hom[ v₁ , v₃ ] (h₁ ⊚ h₂) (k₁ ⊚ k₂)


  -- Interchange
  field
    interchange : ∀ {A B C D E F G H K f g h x y z k}
      {u : Hom A D} {v : Hom B E} {w : Hom C F}
      {l : Ob[ H , K ]} {m : Ob[ G , H ]}
      (α : Hom[ v , w ] f h) → (β : Hom[ u , v ] g k) →
      (γ : Hom[ y , z ] h l) → (δ : Hom[ x , y ] k m) →
      (γ ⊡ δ ∘' α ⊡ β) ≡ (γ ∘' α) ⊡ (δ ∘' β)

  infixr 40 _⊚_
  infixr 50 _⊡_

  field
    λ≅[_] : ∀ {x y} (h : Ob[ x , y ]) → e ⊚ h ≅↓ h
    ρ≅[_] : ∀ {x y} (h : Ob[ x , y ]) → h ⊚ e ≅↓ h
    κ≅[_,_,_] : ∀ {x y z w} (f : Ob[ z , w ]) (g : Ob[ y , z ]) (h : Ob[ x , y ])
      → f ⊚ g ⊚ h  ≅↓ (f ⊚ g) ⊚ h

  λ→ : ∀ {x y} (h : Ob[ x , y ]) → Hom[ id , id ] (e ⊚ h) h
  λ→ h = λ≅[ h ] .to'

  ρ→ : ∀ {x y} (h : Ob[ x , y ]) → Hom[ id , id ] (h ⊚ e) h
  ρ→ h = ρ≅[ h ] .to'

  κ→ : ∀ {x y z w} (f : Ob[ z , w ]) (g : Ob[ y , z ]) (h : Ob[ x , y ])
      → Hom[ id , id ] (f ⊚ g ⊚ h)  ((f ⊚ g) ⊚ h)
  κ→ f g h = κ≅[ f , g , h ] .to'


  field
    λ-nat : ∀ {x y z w u v}
      {h : Ob[ x , y ]} {f : Ob[ w , z ]} →
      (α : Hom[ u , v ] h f) →
      PathP (λ i → Hom[ (C.id-comm {f = u} i) , (C.id-comm {f = v} i) ] (e ⊚ h) f)
      (α ∘' λ→ h) (λ→ f ∘' id[ v ] ⊡ α)

    ρ-nat : ∀ {x y z w u v}
      {h : Ob[ x , y ]} {f : Ob[ w , z ]} →
      (α : Hom[ u , v ] h f) →
      PathP (λ i → Hom[ (C.id-comm {f = u} i) , (C.id-comm {f = v} i) ] (h ⊚ e) f)
      (α ∘' ρ→ h) (ρ→ f ∘' α ⊡ id[ u ])

    κ-nat : ∀ {A B C D E F G H f g h k l m}
      {u : Hom A C} {v : Hom B D} {w : Hom E F} {s : Hom G H}
      (α : Hom[ v , w ] f k) →
      (β : Hom[ u , v ] g l) →
      (γ : Hom[ s , u ] h m) →
      PathP (λ i → Hom[ (C.id-comm {f = s} i) , (C.id-comm {f = w} i) ] (f ⊚ (g ⊚ h)) ((k ⊚ l) ⊚ m))
      ((α ⊡ β) ⊡ γ ∘' κ→ f g h) (κ→ k l m ∘' α ⊡ (β ⊡ γ))

  field
    triangle : ∀ {A B C}
      {f : Ob[ B , C ]} {g : Ob[ A , B ]} →
      PathP (λ i → Hom[ C.id2 (~ i) , C.id2 (~ i) ] (f ⊚ (e ⊚ g)) (f ⊚ g))
      (id' ⊡ λ→ g) (ρ→ f ⊡ id' ∘' κ→ f e g)

    pentagon : ∀ {A B C D E}
      {f : Ob[ D , E ]} {g : Ob[ C , D ]} {h : Ob[ B , C ]} {k : Ob[ A , B ]} →
      PathP (λ i → Hom[ id ∘ C.id2 (~ i) , id ∘ C.id2 (~ i) ] (f ⊚ g ⊚ h ⊚ k) (((f ⊚ g) ⊚ h) ⊚ k))
      (κ→ _ _ _ ∘' κ→ _ _ _) (κ→ _ _ _ ⊡ id' ∘' κ→ _ _ _ ∘' id' ⊡ κ→ _ _ _)
```
