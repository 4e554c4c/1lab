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
open import Cat.Functor.Univalence
open import Cat.Functor.Naturality
open import Cat.Instances.Discrete
open import Cat.Displayed.Cocartesian.Identity
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
open import Cat.Displayed.Univalence
open import Cat.Displayed.Univalence.Reasoning

import Cat.Displayed.IsoFibration
import Cat.Displayed.Cocartesian
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism
import Cat.Reasoning as CR
import Cat.Displayed.Fibre.Reasoning as FR

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

  m n k : Nat

module _ (M : Multicat o ℓ) where
  open Multicat M
  --open DU disp

  open is-identity-system

  module Fibre = FR disp
  open CR Δ∙

  -- basically ℰ[n]=ℰ[1]^n
  open Equivalence
  open Functor
  open Cocartesian-lift
  my-silly-functor : ∀ {n} → Functor (Fibre disp n) Cat[ ( Disc' $ el! $ Fin n) , Fibre disp 1 ]
  my-silly-functor {n} .F₀ o = Disc'-adjunct λ i → o ![ i ]
  my-silly-functor {n} .F₁ {v} {w} f = Disc-natural λ i → lift-ρ.universal' v i Δ∙.id-comm-sym $ f M![ i ]
  my-silly-functor {n} .F-id {v} = ext λ i → begin[]
    (lift-ρ.universal' v i Δ∙.id-comm-sym $ E.id' M![ i ])
      ≡[]⟨⟩
    (lift-ρ.universal' v i Δ∙.id-comm-sym $ lift-ρ.lifting v i E.∘' E.id')
      ≡[]˘⟨ lift-ρ.uniquep v i Δ∙.id-comm-sym refl Δ∙.id-comm-sym E.id' id-comm' ⟩
    E.id'
      ∎[]
  my-silly-functor .F-∘ {x} {y} {z} f' g' = ext λ i → begin[]
    lift-ρ.universal' x i id-comm-sym ((hom[ idl id ] $ f' ∘' g') M![ i ])
      ≡[]⟨ lift-ρ.uniquep x i id-comm-sym refl _ _ $ begin[]
        lift-ρ.universal' x i id-comm-sym (hom[ idl id ] (f' E.∘' g') M![ i ])
        ∘' lift-ρ.lifting x i
          ≡[]⟨ lift-ρ.commutesp x i id-comm-sym (hom[ idl id ] (f' E.∘' g') M![ i ]) ⟩
        hom[ idl id ] (f' E.∘' g') M![ i ]
          ≡[]˘⟨ refl⟩∘'⟨ coh[ idl id ] (f' E.∘' g') ⟩
        (f' E.∘' g') M![ i ]
          ∎[]
      ⟩
    lift-ρ.universal' x i (idl _ ∙ intror (idl id)) ((f' ∘' g') M![ i ])
      ≡[]˘⟨ lift-ρ.uniquep x i (eliml (idl id) ∙ intror (idl id)) (idl id) (idl _ ∙ intror (idl id)) _ $ begin[]
        (lift-ρ.universal' y i id-comm-sym (f' M![ i ]) ∘'
        lift-ρ.universal' x i id-comm-sym (g' M![ i ])) ∘'
        lift-ρ.lifting x i
          ≡[]˘⟨ assoc' _ _ _ ⟩
        lift-ρ.universal' y i id-comm-sym (f' M![ i ]) ∘'
        lift-ρ.universal' x i id-comm-sym (g' M![ i ]) ∘'
        lift-ρ.lifting x i
          ≡[]⟨ refl⟩∘'⟨ lift-ρ.commutesp x i id-comm-sym (g' M![ i ]) ⟩
        lift-ρ.universal' y i id-comm-sym (f' M![ i ]) ∘' g' M![ i ]
          ≡[]⟨⟩
        lift-ρ.universal' y i id-comm-sym (f' M![ i ]) ∘' (lift-ρ.lifting y i ∘' g')
          ≡[]⟨ assoc' _ _ _ ⟩
        (lift-ρ.universal' y i id-comm-sym (f' M![ i ]) ∘' lift-ρ.lifting y i) ∘' g'
          ≡[]⟨ lift-ρ.commutesp y i id-comm-sym (f' M![ i ]) ⟩∘'⟨refl ⟩
        (f' M![ i ]) ∘' g'
          ≡[]˘⟨ assoc' _ _ _ ⟩
        (f' ∘' g') M![ i ]
          ∎[]
      ⟩
    lift-ρ.universal' y i Δ∙.id-comm-sym (f' M![ i ]) ∘'
    lift-ρ.universal' x i Δ∙.id-comm-sym (g' M![ i ])
      ≡[]⟨ coh[ Δ∙.idr _ ] _ ⟩
    (hom[ Δ∙.idr _ ] $
      lift-ρ.universal' y i Δ∙.id-comm-sym (f' M![ i ]) ∘'
      lift-ρ.universal' x i Δ∙.id-comm-sym (g' M![ i ]))
      ∎[]

  hom-extp
    : {f g : ⟨ m ⟩→⟨ n ⟩} {p : f ≡ g} →
    {A : Ob[ m ]} {B : Ob[ n ]}
    {F : Hom[ f ] A B}
    {G : Hom[ g ] A B}
    → (∀ i → F M![ i ] ≡[ refl⟩∘⟨ p ] G M![ i ]) → F ≡[ p ] G
  hom-extp {f = f} {g} {p} {A} {B} {F} {G} ps = begin[]
    F
    ≡[]˘⟨ equiv→unit idx-is-eqv F ⟩
    vec→hom (λ i → F M![ i ])
    ≡[]⟨ (apd (λ i → vec→hom {f = p i}) λ i j → ps j i) ⟩
    vec→hom (λ i → G M![ i ])
    ≡[]⟨ equiv→unit idx-is-eqv G ⟩
    G
    ∎[]


{-
  open is-precat-iso
  open _=>_
  it's-iso : ∀ {n} → is-precat-iso $ my-silly-functor {n}
  it's-iso {n} .has-is-ff {x} {y} .is-eqv nt .centre .fst = idx-is-eqv {n} {n} {x} {y} {Δ∙.id} .is-eqv {! nt .η !} .centre .fst
  it's-iso .has-is-ff .is-eqv y .centre .snd = {! !}
  it's-iso .has-is-ff .is-eqv y .paths = {! !}
  it's-iso .has-is-iso .is-eqv y .centre .fst = vec→ob (λ i → y .F₀ i) .fst
  it's-iso .has-is-iso .is-eqv y .centre .snd = Functor-is-category is-cat .to-path
    $ Disc-natural-iso λ i → Fibre.iso→isof
    $ cocartesian-codomain-unique
      (lift-ρ.cocartesian _ i)
      (vec→ob (λ i → y .F₀ i) .snd i .snd)
  it's-iso .has-is-iso .is-eqv y .paths (o[n] , path) = Σ-pathp {! !} {! !}

  pf : is-category-displayed
  pf = is-category-fibrewise' (Δ∙-gaunt .is-gaunt.has-category) λ n →
    {! !}
-}
open Multicat using (disp)
module _ (M N : Multicat o ℓ) (m-cat : is-category-displayed (M .disp)) (n-cat : is-category-displayed (N .disp))where
  module M = Multicat M
  module N = Multicat N
  --open DU disp

  open is-identity-system

  --module Fibre = FR disp
  open CR Δ∙

  -- basically ℰ[n]=ℰ[1]^n
  open Equivalence
  open Functor
  --open Cocartesian-lift

  UMulticat-path : (M .disp) ≡ (N .disp) → M ≡ N
  UMulticat-path p = Multicat-pathp p $ is-prop-i0→pathp (λ M' N' →
    Multicat-over-pathp
      (ext λ _ _ _ → Cocartesian-lift-is-prop M.disp m-cat _ _ _)
      (ext λ v → Σ-pathp
        (vertical-iso→path (M .disp) (m-cat) record where
            module N' = Multicat-over N'
            module M' = Multicat-over M'
            open M'
            to' = N'.vec→hom λ i → hom[ Δ∙.id-comm-sym ] $ N'.vec→ob!≅vec v i .from' ∘' M'.vec→ob v .snd i .fst
            from' = M'.vec→hom λ i → hom[ Δ∙.id-comm-sym ] $ M'.vec→ob!≅vec v i .from' ∘' N'.vec→ob v .snd i .fst
            inverses' = record
              { invl' = begin[]
                (N'.vec→hom λ i → hom[ Δ∙.id-comm-sym ] $ N'.vec→ob!≅vec v i .M.from' ∘' M'.vec→ob v .snd i .fst)
                ∘' (M'.vec→hom λ i → hom[ Δ∙.id-comm-sym ] $ M'.vec→ob!≅vec v i .M.from' ∘' N'.vec→ob v .snd i .fst)
                ≡[]⟨ hom-extp M (λ j → begin[]
                  ((N'.vec→hom λ i → hom[ Δ∙.id-comm-sym ] $ N'.vec→ob!≅vec v i .M.from' ∘' M'.vec→ob v .snd i .fst)
                  ∘' (M'.vec→hom λ i → hom[ Δ∙.id-comm-sym ] $ M'.vec→ob!≅vec v i .M.from' ∘' N'.vec→ob v .snd i .fst)) M.M![ j ]
                  ≡[]⟨ ? ⟩
                  (N'.vec→hom λ i → hom[ Δ∙.id-comm-sym ] $ N'.vec→ob!≅vec v i .M.from' ∘' M'.vec→ob v .snd i .fst) M.M![ j ]
                  ∘' (M'.vec→hom λ i → hom[ Δ∙.id-comm-sym ] $ M'.vec→ob!≅vec v i .M.from' ∘' N'.vec→ob v .snd i .fst)
                  ≡[]⟨ ? ⟩
                  {! (hom[ Δ∙.id-comm-sym ] $ N'.vec→ob!≅vec v j .M.from' ∘' M'.vec→ob v .snd j .fst)  !}
                  ∘' (M'.vec→hom λ i → hom[ Δ∙.id-comm-sym ] $ M'.vec→ob!≅vec v i .M.from' ∘' N'.vec→ob v .snd i .fst)
                  ≡[]⟨ ? ⟩
                  M.lift-ρ.lifting (N'.vec→ob v .fst) j
                  ≡[]⟨ ? ⟩
                  id' M.M![ j ]
                  ∎[])
                ⟩
                id'
                ∎[]
              ; invr' = {! !}
              }
        )
        {! ? !}
      )
    ) _ _
```
