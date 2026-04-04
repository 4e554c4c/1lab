```agda
open import Cat.Prelude

open import Cat.Functor.Base
open import Cat.Instances.Dist
open import Cat.Displayed.Multi.Base
open import Cat.Functor.Naturality
open import Cat.Functor.Compose renaming (_◆_ to _◇_)
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base

open import Cat.Bi.Base
open import Cat.Bi.Univalent
open import Cat.Displayed.Total
open import Cat.Displayed.Functor
open import Cat.Functor.Univalence
open import Cat.Bi.Diagram.Adjunction
open import Cat.Displayed.Univalence
open import Cat.Displayed.Univalence.Reasoning
open import Cat.Bi.AdjointEquiv
open import Cat.Functor.Adjoint.Unique
open import Cat.Displayed.Functor
open import Cat.Functor.Equivalence.Path

import Cat.Functor.Equivalence as FunEquiv
import Cat.Functor.Reasoning as Fr

import Cat.Reasoning as Cr
import Cat.Displayed.Reasoning as Dr
import Cat.Displayed.Morphism as Dm

open import Cat.Univalent
```
-->

```agda
module Cat.Displayed.Functor.Univalence {o ℓ os ℓs od ℓd : Level} {B : Precategory o ℓ}
  (C : Displayed B os ℓs) (D : Displayed B od ℓd) (univ : is-category-displayed D)
  where
```

<!--
```agda
open Cr B
private
  module C = Dr C
  open module D = Dr D
  module [C,D] = Cr Cat↓[ C , D ]

open Dm D
open Vertical-functor
open _=[_]=>_
```
-->


```agda

Vertical-functor-is-category : is-category Cat↓[ C , D ]
Vertical-functor-is-category .to-path {F} {G} im = Vertical-functor-path (λ x' → vertical-iso→path D univ $ isos x')  λ {x' = x'} {y'} f' →
    Hom[]-pathp-iso D univ (idl _ ∙ idr _) (isos _) (isos _) (F .F₁' f') (G .F₁' f') $ begin[]
    im.to .η' y' ∘' F .F₁' f' ∘' im.from .η' x'
    ≡[]⟨ extendl[] id-comm-sym $ im.to .is-natural' x' y' f' ⟩
    G .F₁' f' ∘' im.to .η' x' ∘' im.from .η' x'
    ≡[]⟨ elimr[] (idl _) $ to-pathp[] $ im.invl η↓ₚ x' ⟩
    G .F₁' f'
    ∎[]
  module to-path where
  module im = [C,D]._≅_ im
  isos : ∀ {x} (x' : C.Ob[ x ]) → F .F₀' x' ≅↓ G .F₀' x'
  isos x' = record where
    to' = im.to .η' x'
    from' = im.from .η' x'
    inverses' = record
      { invl' = to-pathp[] $ im.invl η↓ₚ x'
      ; invr' = to-pathp[] $ im.invr η↓ₚ x'
      }
Vertical-functor-is-category .to-path-over {F} {G} p = [C,D].≅-pathp _ _ $ Vertical-Nat-pathp' _ _ λ x' →
   Hom[]-pathp-reflr-iso D univ (idr _) (isos x') _ _ (idr' _)
  where open to-path p
```
