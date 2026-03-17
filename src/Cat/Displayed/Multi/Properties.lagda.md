<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Instances.Simplex.Pointed
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
open import Cat.Functor.Base
open import Cat.Functor.Equivalence
open import Cat.Instances.Discrete
open import Cat.Prelude
open import Cat.Gaunt

open import Data.Product.NAry
open import Data.Maybe.Base
open import Data.Vec.Base
open import Data.Vec.Properties
open import Data.List hiding (lookup-tabulate) renaming (lookup to lookupℓ; tabulate to tabulateℓ)
open import Data.Fin

open import Meta.Idiom

open import Order.Base
open import Order.Cat

import Cat.Displayed.IsoFibration
import Cat.Displayed.Cocartesian
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism
import Cat.Displayed.Univalence as DU
import Cat.Reasoning as CR

import Order.Reasoning

open import Cat.Displayed.Multi.Base
```
-->

```agda
module Cat.Displayed.Multi.Properties where
```

# Displayed multicategories {defines=displayed-multicategory}

```agda
private variable
  o ℓ ℓ' : Level

module _ (M : Multicat o ℓ) where
  open Multicat M public
  open DU disp

  open is-identity-system

  module Fibre = CR (Fibre disp 1)
  is-category[1] : is-category (Fibre disp 1)
  is-category[1] .to-path i = {!(i .Fibre._≅_.to) M![ fzero ] !}
  is-category[1] .to-path-over = {! !}


  -- basically ℰ[n]=ℰ[1]^n
  open Equivalence
  open Functor
  open Cocartesian-lift
  my-silly-functor : ∀ {n} → Functor (Fibre disp n) Cat[ ( Disc' $ el! $ Fin n) , Fibre disp 1 ]
  my-silly-functor {n} .F₀ o = Disc'-adjunct λ i → o ![ i ]
  my-silly-functor {n} .F₁ {v} {w} f = Disc-natural λ i → lift-ρ.universal v i Δ∙.id $ hom[ Δ∙.id-comm ] $ f M![ i ]
  my-silly-functor {n} .F-id {v} = ext λ i → {! !}
  my-silly-functor .F-∘ = {! !}


  open is-precat-iso
  open _=>_
  it's-iso : ∀ {n} → is-precat-iso $ my-silly-functor {n}
  it's-iso {n} .has-is-ff {x} {y} .is-eqv nt .centre .fst = idx-is-eqv {n} {n} {x} {y} {Δ∙.id} .is-eqv {! nt .η !} .centre .fst
  it's-iso .has-is-ff .is-eqv y .centre .snd = {! !}
  it's-iso .has-is-iso = {! !}

  pf : is-category-displayed
  pf = is-category-fibrewise' (Δ∙-gaunt .is-gaunt.has-category) λ n →
    {! !}

```
