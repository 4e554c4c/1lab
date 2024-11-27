<!--
```agda
open import Cat.Functor.Constant
open import Cat.Prelude
open import Cat.Finite

open import Data.Fin.Finite
open import Data.Bool

import Cat.Reasoning
open import Cat.Functor.Equivalence
open import Cat.Functor.Equivalence.Path
```
-->

```agda
module Cat.Instances.Shape.Parallel where
```

# The "parallel arrows" category {defines="parallel-arrows"}

The parallel arrows category is the category with two objects, and two
parallel arrows between them. It is the shape of [[equaliser]] and
[coequaliser] diagrams.

[coequaliser]: Cat.Diagram.Coequaliser.html

```agda

·⇉· : Precategory lzero lzero
·⇉· = precat where
  open Precategory
  precat : Precategory _ _
  precat .Ob = Bool

  precat .Hom false false = ⊤
  precat .Hom false true  = Bool
  precat .Hom true  false = ⊥
  precat .Hom true  true  = ⊤
```

<!--
```agda
  precat .Hom-set false false = hlevel 2
  precat .Hom-set false true  = hlevel 2
  precat .Hom-set true  true  = hlevel 2

  precat .id {false} = tt
  precat .id {true} = tt
  _∘_ precat {false} {false} {false} _ _ = tt
  _∘_ precat {false} {false} {true}  p _ = p
  _∘_ precat {false} {true}  {true}  _ q = q
  _∘_ precat {true}  {true}  {true}  _ _ = tt
  precat .idr {false} {false} f = refl
  precat .idr {false} {true}  f = refl
  precat .idr {true}  {true}  f = refl
  precat .idl {false} {false} f = refl
  precat .idl {false} {true}  f = refl
  precat .idl {true}  {true}  f = refl
  precat .assoc {false} {false} {false} {false} f g h = refl
  precat .assoc {false} {false} {false} {true}  f g h = refl
  precat .assoc {false} {false} {true}  {true}  f g h = refl
  precat .assoc {false} {true}  {true}  {true}  f g h = refl
  precat .assoc {true}  {true}  {true}  {true}  f g h = refl

·⇉·-finite : is-finite-precategory ·⇉·
·⇉·-finite = finite-cat-hom λ where
  true  true  → auto
  true  false → auto
  false true  → auto
  false false → auto

·⇇· = ·⇉· ^op

module ·⇉· = Precategory ·⇉·
module ·⇇· = Precategory ·⇇·

·⇇·≡·⇉· : ·⇇· ≡ ·⇉·
·⇇·≡·⇉· = Precategory-path F F-is-iso where
  open Functor
  F : Functor ·⇇· ·⇉·
  F .F₀ x = not x
  F .F₁ {true} {true} tt = tt
  F .F₁ {true} {false} f = f
  F .F₁ {false} {false} tt = tt
  F .F-id {true} = refl
  F .F-id {false} = refl
  F .F-∘ {true} {true} {true} f g = refl
  F .F-∘ {true} {true} {false} f g = refl
  F .F-∘ {true} {false} {false} f g = refl
  F .F-∘ {false} {false} {false} f g = refl

  open is-precat-iso
  open is-iso

  F-is-iso : is-precat-iso F
  F-is-iso .has-is-ff {true} {true} .is-eqv _ = hlevel 0
  F-is-iso .has-is-ff {true} {false} .is-eqv y .centre = y , refl
  F-is-iso .has-is-ff {true} {false} .is-eqv _ .paths (s , p) = J' (λ s t p → (t , refl) ≡ (s , p)) (λ t → refl) p
  F-is-iso .has-is-ff {false} {false} .is-eqv y = hlevel 0
  F-is-iso .has-is-iso = not-is-equiv
```
-->

```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  open Functor
  open _=>_

  Fork : ∀ {a b} (f g : Hom a b) → Functor ·⇉· C
  Fork f g = funct where
    funct : Functor _ _
    funct .F₀ false = _
    funct .F₀ true = _
    funct .F₁ {false} {false} _ = id
    funct .F₁ {false} {true}  false = f
    funct .F₁ {false} {true}  true = g
    funct .F₁ {true} {true}   _ = id
    funct .F-id {false} = refl
    funct .F-id {true} = refl
    funct .F-∘ {false} {false} {false} f g   = sym (idr _)
    funct .F-∘ {false} {false} {true}  f g   = sym (idr _)
    funct .F-∘ {false} {true}  {true}  tt _  = sym (idl _)
    funct .F-∘ {true}  {true}  {true}  tt tt = sym (idl _)

  forkl : (F : Functor ·⇉· C) → Hom (F .F₀ false) (F .F₀ true)
  forkl F = F .F₁ {false} {true} false

  forkr : (F : Functor ·⇉· C) → Hom (F .F₀ false) (F .F₀ true)
  forkr F = F .F₁ {false} {true} true

  Fork→Cone
    : ∀ {e} (F : Functor ·⇉· C) {equ : Hom e (F .F₀ false)}
    → forkl F ∘ equ ≡ forkr F ∘ equ
    → Const e => F
  Fork→Cone {e = e} F {equ = equ} equal = nt where
    nt : Const e => F
    nt .η true = forkl F ∘ equ
    nt .η false = equ
    nt .is-natural true true tt = idr _ ∙ introl (F .F-id)
    nt .is-natural false true true = idr _ ∙ equal
    nt .is-natural false true false = idr _
    nt .is-natural false false tt = idr _ ∙ introl (F .F-id)

  Cofork→Cocone
    : ∀ {e} (F : Functor ·⇉· C) {coequ : Hom (F .F₀ true) e}
    → coequ ∘ forkl F ≡ coequ ∘ forkr F
    → F => Const e
  Cofork→Cocone {e = e} F {coequ} coequal = nt where
    nt : F => Const e
    nt .η true = coequ
    nt .η false = coequ ∘ forkl F
    nt .is-natural true true tt = elimr (F .F-id) ∙ sym (idl _)
    nt .is-natural false true true = sym coequal ∙ sym (idl _)
    nt .is-natural false true false = sym (idl _)
    nt .is-natural false false tt = elimr (F .F-id) ∙ sym (idl _)
```
