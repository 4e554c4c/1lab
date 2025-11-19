<!--
```agda
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Product
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
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
record DoubleCategoryOver {C : Precategory o ℓ} (E : Displayed (C ×ᶜ C) ℓv ℓ□) : Type (lsuc (o ⊔ ℓ ⊔ ℓv ⊔ ℓ□)) where
  open module C = Cat.Reasoning C public
  module C² = Cat.Reasoning (C ×ᶜ C)
  open Cat.Displayed.Reasoning E public
  open Cat.Displayed.Morphism E
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


record DoubleFunctorOver
    {C : Precategory o ℓ} {C' : Precategory o ℓ}
    (E : Displayed (C ×ᶜ C) ℓv ℓ□) (E' : Displayed (C' ×ᶜ C') ℓv ℓ□)
    (F : Functor C C') (𝔉 : Displayed-functor (F F× F)  E E')
    (D : DoubleCategoryOver E) (D' : DoubleCategoryOver E')
    : Type (lsuc (o ⊔ ℓ ⊔ ℓv ⊔ ℓ□)) where
  module C = Cat.Reasoning C
  module C' = Cat.Reasoning C'
  open module F = Functor F public
  open module 𝔉 = Displayed-functor 𝔉 public
  module D = DoubleCategoryOver D
  module D' = DoubleCategoryOver D'
  field
    F-e : ∀ {x} → F₀' (D.e {x}) ≡ D'.e

    F-id[_] : ∀ {x y} (h : C.Hom x y) →
      PathP (λ i → D'.Hom[ F₁ h , F₁ h ] (F-e i) (F-e i))
        (F₁' D.id[ h ])
        D'.id[ F₁ h ]

    F-⊚ : ∀ {x y z} (f : D.Ob[ y , z ]) (g : D.Ob[ x , y ]) →
      F₀' (f D.⊚ g ) ≡ F₀' f D'.⊚ F₀' g

    F-⊡ : ∀ {a b c d e f v₁ v₂ v₃}
      {h₁ : D.Ob[ b , c ]} {h₂ : D.Ob[ a , b ]}
      {k₁ : D.Ob[ e , f ]} {k₂ : D.Ob[ d , e ]} →
      (α : D.Hom[ v₂ , v₃ ] h₁ k₁) (β : D.Hom[ v₁ , v₂ ] h₂ k₂) →
        PathP (λ i → D'.Hom[ F₁ v₁ , F₁ v₃ ] (F-⊚ h₁ h₂ i) (F-⊚ k₁ k₂ i))
        (F₁' (α D.⊡ β))
        (F₁' α D'.⊡ F₁' β)

record DoubleCategory : Type (lsuc (o ⊔ ℓ ⊔ ℓv ⊔ ℓ□)) where
  field
    {Ver} : Precategory o ℓ
    𝔘 : Displayed (Ver ×ᶜ Ver) ℓv ℓ□
    structure : DoubleCategoryOver 𝔘
  open DoubleCategoryOver structure public

record DoubleFunctor (D : DoubleCategory) (D' : DoubleCategory) : Type (lsuc (o ⊔ ℓ ⊔ ℓv ⊔ ℓ□)) where
  module D = DoubleCategory D
  module D' = DoubleCategory D'
  field
    Fᵥ : Functor D.Ver D'.Ver
    𝔉 : Displayed-functor (Fᵥ F× Fᵥ) D.𝔘 D'.𝔘
    U : DoubleFunctorOver D.𝔘 D'.𝔘 Fᵥ 𝔉 D.structure D'.structure
```
