<!--
```agda
open import Cat.Instances.FinSets.Kleisli
open import Cat.Displayed.BeckChevalley
open import Cat.Diagram.Limit.Finite
open import Cat.Displayed.Functor
open import Cat.Instances.Product
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Morphism.Class
open import Cat.Prelude

open import Data.Product.NAry
open import Data.Maybe.Base
open import Data.Vec.Base
open import Data.Vec.Properties
open import Data.List hiding (lookup)
open import Data.Fin

open import Meta.Idiom

open import Order.Base
open import Order.Cat

import Cat.Displayed.IsoFibration
import Cat.Displayed.Cocartesian
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism
import Cat.Reasoning

import Order.Reasoning
```
-->

```agda
module Cat.Displayed.Operad  where

private variable
  o ℓ : Level
```

<!--
```agda
```
-->

# multi cats

```agda
open Precategory Fin∙Sets using () renaming (Hom to ⟨_⟩→⟨_⟩)

record Operad-over (E : Displayed Fin∙Sets o ℓ)  : Type (lsuc (o ⊔ ℓ)) where
  open module E = DR E public
  open Cat.Displayed.Cocartesian E public
  open Cat.Displayed.IsoFibration E
  open Cocartesian-lift

  field
    lift-inert : ∀ {m n} → (f : ⟨ m ⟩→⟨ n ⟩) → (is-inert f) → ∀ C → Cocartesian-lift f C
    lift-iso : Isofibration

  Ob : Type o
  Ob = Ob[ 1 ]

  -- A : Ob[ m ] is a "vec" of colors
  _![_] : ∀ {m} → (A : Ob[ m ]) → (i : Fin m) → Ob
  L ![ k ] = lift-inert ρ[ k ] (ρ-inert {k = k}) L .y'

  -- likewise morphisms are vecs of multiarrows
  _M![_] : ∀ {m n} {A : Ob[ m ]} {B : Ob[ n ]} → {f : ⟨ m ⟩→⟨ n ⟩}
    → Hom[ f ] A B → (i : Fin n) → Hom[ ρ[ i ] <=< f ] A (B ![ i ])
  _M![_] {A = A} {B = B} {f = f} h k = lift-inert ρ[ k ] (ρ-inert {k = k}) B .lifting ∘' h

  -- this transformation should be an equivalence
  field
    idx-is-eqv : ∀ {m n} {A : Ob[ m ]} {B : Ob[ n ]} → {f : ⟨ m ⟩→⟨ n ⟩} → is-equiv (_M![_] {m} {n} {A} {B} {f})

  -- finally, we can lift vecs to elements of E
    vec→ob : ∀ {n} (C[_] : (Fin n) → Ob) →
      Σ[ C ∈ Ob[ n ] ] ((k : Fin n) → Σ[ f ∈ Hom[ ρ[ k ] ] C C[ k ] ] is-cocartesian ρ[ k ] f)

module _ {ℰ : Displayed Fin∙Sets o ℓ} {ℱ : Displayed Fin∙Sets o ℓ} (O : Operad-over ℰ) (M : Operad-over ℱ) where
  private
    module O = Operad-over O
    module M = Operad-over M

  record OperadFunctorOver : Type (lsuc (o ⊔ ℓ)) where
    field
      U : Displayed-functor Id ℰ ℱ
    open Displayed-functor U public
    field
      preserves-inert
        : ∀ {a b a' b'} {f : ⟨ a ⟩→⟨ b ⟩} {f' : O.Hom[ f ] a' b'}
        → f ∈ Inert
        → O.is-cocartesian f f'
        → M.is-cocartesian f (F₁' f')

record Operad (o ℓ : Level) : Type (lsuc (o ⊔ ℓ)) where
  field
    ℰ : Displayed Fin∙Sets o ℓ
    is-operad : Operad-over ℰ

list-fibre : ∀ {n m} (f : ⟨ n ⟩→⟨ m ⟩) → (k : Fin m) → Listing (fibre f (just k))
list-fibre f k = auto

record make-operad (o ℓ : Level) : Type (lsuc (o ⊔ ℓ)) where
  field
    Ob : Type o
    Homl : List Ob → Ob → Type ℓ
    Homl-is-set : ∀ xs y → is-set $ Homl xs y

    id : ∀ (x : Ob) → Homl [ x ] x

  ΣHoml = Σ[ xs ∈ List Ob ] Σ[ y ∈ Ob ] Homl xs y

  field
    comp-homl
      : ∀ {n} (xxs : Vec (List Ob) n) (ys : Vec Ob n) (z : Ob)
      → (∀ j → Homl (lookup xxs j) (lookup ys j))
      → Homl (lower ys) z
      → Homl (concat $ lower xxs) z
