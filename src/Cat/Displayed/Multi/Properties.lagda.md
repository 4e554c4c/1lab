<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Instances.Dist
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
import Cat.Displayed.Cocartesian as Coc
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
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM
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

module _ (E : Displayed Dist o ℓ) (lift-inert : Coc.Cocartesian-lifts-of E Inert) (M : Multicat-over E lift-inert) where
  open Multicat-over M

  open is-identity-system

  module Fibre = FR E
  open CR Dist

  -- basically ℰ[n]=>ℰ[1]^n, iff it's an iso we have univalence
  open Equivalence
  open Functor
  open Cocartesian-lift
  fibre-func : ∀ {n} → Functor (Fibre E n) Cat[ ( Disc' $ el! $ Fin n) , Fibre E 1 ]
  fibre-func {n} .F₀ o = Disc'-adjunct λ i → o ![ i ]
  fibre-func {n} .F₁ {v} {w} f = Disc-natural λ i → lift-ρ.universal' v i Dist.id-comm-sym $ f M![ i ]
  fibre-func {n} .F-id {v} = ext λ i → begin[]
    (lift-ρ.universal' v i Dist.id-comm-sym $ E.id' M![ i ])
      ≡[]⟨⟩
    (lift-ρ.universal' v i Dist.id-comm-sym $ lift-ρ.lifting v i E.∘' E.id')
      ≡[]˘⟨ lift-ρ.uniquep v i Dist.id-comm-sym refl Dist.id-comm-sym E.id' id-comm' ⟩
    E.id'
      ∎[]
  fibre-func .F-∘ {x} {y} {z} f' g' = ext λ i → begin[]
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
    lift-ρ.universal' y i Dist.id-comm-sym (f' M![ i ]) ∘'
    lift-ρ.universal' x i Dist.id-comm-sym (g' M![ i ])
      ≡[]⟨ coh[ Dist.idr _ ] _ ⟩
    (hom[ Dist.idr _ ] $
      lift-ρ.universal' y i Dist.id-comm-sym (f' M![ i ]) ∘'
      lift-ρ.universal' x i Dist.id-comm-sym (g' M![ i ]))
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

  hom-idextp :
    {A : Ob[ n ]} {B : Ob[ n ]}
    {F : Hom[ id ] A B}
    {G : Hom[ id ] A B}
    → (∀ i → F !![ i ] ≡ G !![ i ]) → F ≡ G
  hom-idextp {A = A} {B} {F} {G} ps = hom-extp λ k → begin[]
    F M![ k ]
    ≡[]˘⟨ lift-ρ.commutesp A k (idl _) (F M![ k ]) ⟩
    (lift-ρ.universal' A k (idl _) $ F M![ k ]) ∘' lift-ρ.lifting A k
    ≡[]⟨⟩
    F !![ k ] ∘' lift-ρ.lifting A k
    ≡[]⟨ ps k ⟩∘'⟨refl ⟩
    G !![ k ] ∘' lift-ρ.lifting A k
    ≡[]⟨⟩
    (lift-ρ.universal' A k (Dist.idl _) $ G M![ k ]) ∘' lift-ρ.lifting A k
    ≡[]⟨ lift-ρ.commutesp A k (idl _) (G M![ k ])  ⟩
    G M![ k ]
    ∎[]

  idextp-comp :
    {p : id ∘ id ≡ id}
    {A : Ob[ n ]} {B : Ob[ n ]} {C : Ob[ n ]}
    {G : Hom[ id ] A B}
    {F : Hom[ id ] B C}
    → ∀ k → F !![ k ] ∘' G !![ k ] ≡[ p ] (F ∘' G) !![ k ]
  idextp-comp {A = A} {B} {C} {G} {F} k = begin[]
    F !![ k ] ∘' G !![ k ]
    ≡[]⟨⟩
    (lift-ρ.universal' B k (idl _) $ F M![ k ])
    ∘' (lift-ρ.universal' A k (idl _) $ G M![ k ])
    ≡[]⟨ lift-ρ.uniquep A k (idl _) (idl _) _ _ $ begin[]
        ((lift-ρ.universal' B k (idl _) $ F M![ k ])
        ∘' (lift-ρ.universal' A k (idl _) $ G M![ k ]))
        ∘' lift-ρ.lifting A k
        ≡[]⟨ pullr[] _ $ lift-ρ.commutesp A k (idl _) (G M![ k ])  ⟩
        (lift-ρ.universal' B k (idl _) $ F M![ k ])
        ∘' G M![ k ]
        ≡[]⟨⟩
        (lift-ρ.universal' B k (idl _) $ F M![ k ])
        ∘' lift-ρ.lifting B k ∘' G
        ≡[]⟨ extendl[] _ $ lift-ρ.commutesp B k (idl _) (F M![ k ])  ⟩
        (F ∘' G) M![ k ]
        ∎[]
    ⟩
    (lift-ρ.universal' A k (idl _) $ (F ∘' G) M![ k ])
    ≡[]⟨⟩
    (F ∘' G) !![ k ]
    ∎[]

  idextp-id :
    {A : Ob[ n ]}
    → ∀ {k} → id' {n} {A} !![ k ] ≡ id'
  idextp-id {A = A} {k} = sym $ lift-ρ.uniquep A k (idl _) _ _ _ $ begin[]
    id' ∘' lift-ρ.lifting A k
    ≡[]⟨ idl' _ ⟩
    lift-ρ.lifting A k
    ≡[]˘⟨ idr' _ ⟩
    id' M![ k ]
    ∎[]

module _ (E : Displayed Dist o ℓ) (lift-inert : Coc.Cocartesian-lifts-of E Inert) (is-cat : is-category-displayed E) (M N : Multicat-over E lift-inert) where
  open DR E
  private
    module M = Multicat-over M
    module N = Multicat-over N
  open CR Dist hiding (Ob)
  open DM E
  open _≅[_]_ renaming (from' to f' ; to' to t')
  open M using (Ob ; _![_] ; _M![_] ; _!![_]; module lift-ρ)
  Multicat-over-is-prop : M ≡ N
  Multicat-over-is-prop = Multicat-over-pathp (ext λ v → p₁ v) $ funextP' λ {n} → funextP λ C[_] → funextP λ j → N.Cocartesian-morphism-pathp $
    Hom[]-pathp-refll-iso E is-cat (idr _) (da_iso C[_]) (M.vec-proj.hom' C[_] j) (N.vec-proj.hom' C[_] j) $ begin[]
      M.vec-proj.hom' C[_] j ∘' N.vec→hom' (λ k → M.vec→ob!≅vec.from' C[_] k ∘' N.vec→ob!≅vec.to' C[_] k)
      ≡[]˘⟨ pulll[] _ $ lift-ρ.commutesp (M.vec→ob C[_]) j (idl _) $ M.vec-proj.hom' C[_] j ⟩
      M.vec→ob!≅vec.to' C[_] j ∘' lift-ρ.lifting (M.vec→ob C[_]) j ∘' N.vec→hom' (λ k → M.vec→ob!≅vec.from' C[_] k ∘' N.vec→ob!≅vec.to' C[_] k)
      ≡[]⟨⟩
      M.vec→ob!≅vec.to' C[_] j ∘' (N.vec→hom' (λ k → M.vec→ob!≅vec.from' C[_] k ∘' N.vec→ob!≅vec.to' C[_] k) M![ j ])
      ≡[]⟨ refl⟩∘'⟨ equiv→counit N.idx-is-eqv _ · j ⟩
      M.vec→ob!≅vec.to' C[_] j ∘' (hom[ id-comm-sym ] $ (M.vec→ob!≅vec.from' C[_] j ∘' N.vec→ob!≅vec.to' C[_] j) ∘' lift-ρ.lifting (N.vec→ob C[_]) j)
      ≡[]˘⟨ refl⟩∘'⟨ coh[ id-comm-sym ] _ ⟩
      M.vec→ob!≅vec.to' C[_] j ∘' ((M.vec→ob!≅vec.from' C[_] j ∘' N.vec→ob!≅vec.to' C[_] j) ∘' lift-ρ.lifting (N.vec→ob C[_]) j)
      ≡[]˘⟨ refl⟩∘'⟨ assoc' _ _ _ ⟩
      M.vec→ob!≅vec.to' C[_] j ∘' M.vec→ob!≅vec.from' C[_] j ∘' N.vec→ob!≅vec.to' C[_] j ∘' lift-ρ.lifting (N.vec→ob C[_]) j
      ≡[]⟨ cancell[] _ $ M.vec→ob!≅vec.invl' C[_] j ⟩
      N.vec→ob!≅vec.to' C[_] j ∘' lift-ρ.lifting (N.vec→ob C[_]) j
      ≡[]⟨ lift-ρ.commutesp (N.vec→ob C[_]) j (idl _) $ N.vec-proj.hom' C[_] j ⟩
      N.vec-proj.hom' C[_] j
      ∎[]
    where
      da_iso : ∀ {n} (C[_] : (Fin n) → Ob) → M.vec→ob C[_] ≅↓ N.vec→ob C[_]
      da_iso {n} C[_] = let C = M.vec→ob C[_] in let C' = N.vec→ob C[_] in record where
            to' = N.vec→hom' λ k → N.vec→ob!≅vec.from' C[_] k ∘' M.vec→ob!≅vec.to' C[_] k
            from' = N.vec→hom' λ k → M.vec→ob!≅vec.from' C[_] k ∘' N.vec→ob!≅vec.to' C[_] k
            inverses' : Inverses[ _ ] to' from'
            inverses' = record where
              invl' = begin[]
                to' ∘' from'
                ≡[ refl ]⟨(
                  hom-idextp E lift-inert M λ k → begin[]
                  (to' ∘' from') !![ k ]
                  ≡[]˘⟨ idextp-comp E lift-inert N {p = refl} k ⟩
                  to' !![ k ] ∘' from' !![ k ]
                  ≡[]⟨ N.vec-idx' _ k ⟩∘'⟨ N.vec-idx' _ k ⟩
                  (N.vec→ob!≅vec.from' C[_] k ∘' M.vec→ob!≅vec.to' C[_] k)
                  ∘' (M.vec→ob!≅vec.from'  C[_] k ∘' N.vec→ob!≅vec.to' C[_] k)
                  ≡[]⟨ cancel-inner[] _ (M.vec→ob!≅vec.invl' C[_] k) ⟩
                  N.vec→ob!≅vec.from' C[_] k ∘' N.vec→ob!≅vec.to' C[_] k
                  ≡[]⟨ N.vec→ob!≅vec.invr' C[_] k ⟩
                  id'
                  ≡[]˘⟨ idextp-id E lift-inert N ⟩
                  id' !![ k ]
                  ∎[]
                )⟩
                id'
                ∎[]
              invr' = begin[]
                from' ∘' to'
                ≡[ refl ]⟨(
                  hom-idextp E lift-inert M λ k → begin[]
                  (from' ∘' to') !![ k ]
                  ≡[]˘⟨ idextp-comp E lift-inert N {p = refl} k ⟩
                  from' !![ k ] ∘' to' !![ k ]
                  ≡[]⟨ N.vec-idx' _ k ⟩∘'⟨ N.vec-idx' _ k ⟩
                  (M.vec→ob!≅vec.from'  C[_] k ∘' N.vec→ob!≅vec.to' C[_] k)
                  ∘' (N.vec→ob!≅vec.from' C[_] k ∘' M.vec→ob!≅vec.to' C[_] k)
                  ≡[]⟨ cancel-inner[] _ (N.vec→ob!≅vec.invl' C[_] k) ⟩
                  M.vec→ob!≅vec.from' C[_] k ∘' M.vec→ob!≅vec.to' C[_] k
                  ≡[]⟨ M.vec→ob!≅vec.invr' C[_] k ⟩
                  id'
                  ≡[]˘⟨ idextp-id E lift-inert N ⟩
                  id' !![ k ]
                  ∎[]
                )⟩
                id'
                ∎[]
      p₁ : ∀ {n} (C[_] : (Fin n) → Ob) → M.vec→ob C[_] ≡ N.vec→ob C[_]
      p₁ {n} C[_] = let C = M.vec→ob C[_] in let C' = N.vec→ob C[_] in
        vertical-iso→path E is-cat $ da_iso C[_]

open Multicat using (disp)
module _ (M N : Multicat o ℓ) (m-cat : is-category-displayed (M .disp)) (m-cat : is-category-displayed (M .disp))where
  private
    module M = Multicat M
    module N = Multicat N

  open is-identity-system

  open CR Dist

  open Equivalence
  open Functor

  UMulticat-path : (M .disp) ≡ (N .disp) → M ≡ N
  UMulticat-path p = Multicat-pathp p
    (is-prop-i0→pathp (λ _ _ → ext λ _ _ _ → Cocartesian-lift-is-prop _ m-cat _ _ _) _ _)
    (is-prop-i0→pathp (λ _ _ → Multicat-over-is-prop _ _ m-cat _ _) _ _)

```
