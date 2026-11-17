<!--
```agda
--{-# OPTIONS --allow-unsolved-metas #-}
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
open import Cat.Displayed.Functor
open import Cat.Morphism.Class
open import Cat.Prelude
open import Cat.Prelude

open import Data.Product.NAry
open import Data.Maybe.Base
open import Data.Vec.Base
open import Data.Vec.Properties
open import Data.List hiding (lookup-tabulate) renaming (lookup to lookupℓ; tabulate to tabulateℓ)
open import Data.Fin

open import Meta.Idiom

open import Order.Base
open import Order.Cat

import Cat.Displayed.Isofibration
import Cat.Displayed.Cocartesian as Coc
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM
import Cat.Reasoning as Cr

import Order.Reasoning
```
-->

```agda
module Cat.Displayed.Multi.Base where
```

# Displayed multicategories {defines=displayed-multicategory}

```agda
private variable
  o ℓ o' ℓ' : Level

record Multicat-over (E : Displayed Dist o ℓ) (lift-inert : Coc.Cocartesian-lifts-of E Inert)  : Type (lsuc (o ⊔ ℓ)) where
  open Cr Dist hiding (Ob)
  open module E = DR E public
  open Coc E public
  open DM E public
  --open Cat.Displayed.Isofibration E
  open Cocartesian-lift

  module lift-inert {m n} (f : ⟨ m ⟩→⟨ n ⟩)(f-inert : is-inert f) C
    = Cocartesian-lift (lift-inert f f-inert C)

  module lift-ρ {n} (C : Ob[ n ]) k = lift-inert ρ[ k ] (ρ-inert {k = k}) C

  Ob : Type o
  Ob = Ob[ 1 ]

  infixl 50 _![_] _M![_] _!![_]
  -- A : Ob[ m ] is a "vec" of obs
  _![_] : ∀ {m} → (A : Ob[ m ]) → (i : Fin m) → Ob
  L ![ k ] = lift-ρ.y' L k

  -- likewise morphisms are vecs of multiarrows
  _M![_] : ∀ {m n} {A : Ob[ m ]} {B : Ob[ n ]} → {f : ⟨ m ⟩→⟨ n ⟩}
    → Hom[ f ] A B → (i : Fin n) → Hom[ ρ[ i ] ∘ f ] A (B ![ i ])
  _M![_] {A = A} {B = B} {f = f} h k = lift-ρ.lifting B k ∘' h

  -- this transformation should be an equivalence
  field
    idx-is-eqv : ∀ {m n} {A : Ob[ m ]} {B : Ob[ n ]} → {f : ⟨ m ⟩→⟨ n ⟩} → is-equiv (_M![_] {m} {n} {A} {B} {f})

  -- finally, we can lift vecs to elements of E
    ↑ : ∀ {n} (C[_] : (Fin n) → Ob) → Ob[ n ]

    cocart-proj : ∀ {n} (C[_] : (Fin n) → Ob) → (k : Fin n) → Cocartesian-morphism ρ[ k ] (↑ C[_]) C[ k ]

  module cocart-proj {n} (C[_] : (Fin n) → Ob) (k : Fin n)
    = Cocartesian-morphism (cocart-proj C[_] k)

  vec→hom
    : ∀ {m n} {A : Ob[ m ]} {B : Ob[ n ]} → {f : ⟨ m ⟩→⟨ n ⟩}
    → ((i : Fin n) → Hom[ ρ[ i ] ∘ f ] A (B ![ i ])) → Hom[ f ] A B
  vec→hom = equiv→inverse idx-is-eqv

  open Cocartesian-morphism

  ↑!≅vec : ∀ {n} (C[_] : (Fin n) → Ob) → ∀ i →
    ↑ C[_] ![ i ] ≅↓ C[ i ]
  ↑!≅vec C[_] i = cocartesian-codomain-unique
      (lift-ρ.cocartesian _ i)
      (cocart-proj C[_] i .cocartesian)

  module ↑!≅vec {n} C i = _≅[_]_ (↑!≅vec {n} C i)

  _!![_] : ∀ {n} {A : Ob[ n ]} {B : Ob[ n ]}
    → Hom[ id ] A B → (i : Fin n) → Hom[ id ] (A ![ i ]) (B ![ i ])
  _!![_] {A = A} {B = B} h k = lift-ρ.universal' A k (idl _) $ h M![ k ]


  vec→hom'
    : ∀ {n} {A : Ob[ n ]} {B : Ob[ n ]}
    → ((i : Fin n) → Hom[ id ] (A ![ i ]) (B ![ i ])) → Hom[ id ] A B
  vec→hom' {A = A} {B} fs = vec→hom λ i → hom[ id-comm-sym ] $ fs i ∘' lift-ρ.lifting A i


  vec-idx' : ∀ {n} {A : Ob[ n ]} {B : Ob[ n ]}
    → (fs : (i : Fin n) → Hom[ id ] (A ![ i ]) (B ![ i ])) → ∀ k → (vec→hom' fs) !![ k ] ≡ fs k
  vec-idx' {A = A} {B} fs k =  lift-ρ.uniquep A k id-comm-sym _ _ _ $ begin[] 
    fs k ∘' lift-ρ.lifting A k
    ≡[]⟨ coh[ id-comm-sym ] _ ⟩
    (hom[ id-comm-sym ] $ fs k ∘' lift-ρ.lifting A k)
    ≡[]˘⟨ equiv→counit idx-is-eqv _ · k ⟩
    vec→hom' fs M![ k ]
    ∎[]

  idx-vec' : ∀ {n} {A : Ob[ n ]} {B : Ob[ n ]}
    → (F : Hom[ id ] A B) → (vec→hom' λ k → F !![ k ] ) ≡ F
  idx-vec' {A = A} {B = B} F = begin[]
    (vec→hom' λ k → F !![ k ])
    ≡[]⟨⟩
    vec→hom (λ k → hom[ _ ] $ F !![ k ] ∘' lift-ρ.lifting A k)
    ≡[]⟨ (ap vec→hom $ ext λ k → begin[]
      (hom[ _ ] $ F !![ k ] ∘' lift-ρ.lifting A k)
      ≡[]˘⟨ coh[ _ ] _ ⟩
      F !![ k ] ∘' lift-ρ.lifting A k
      ≡[]⟨ lift-ρ.commutesp A k (idl _) (F M![ k ]) ⟩
      F M![ k ]
      ∎[]
    ) ⟩
    vec→hom (λ k → F M![ k ])
    ≡[]⟨ equiv→unit idx-is-eqv F ⟩
    F
    ∎[]


unquoteDecl Multicat-over-pathp = declare-record-path Multicat-over-pathp (quote Multicat-over)

record Multicat (o ℓ : Level) : Type (lsuc (o ⊔ ℓ)) where
  field
    disp : Displayed Dist o ℓ
    lift-inert : Coc.Cocartesian-lifts-of disp Inert
    is-multi : Multicat-over disp lift-inert

  open Multicat-over is-multi public

unquoteDecl Multicat-pathp = declare-record-path Multicat-pathp (quote Multicat)

module _ (O : Multicat o ℓ) (M : Multicat o' ℓ') where
  private
    module O = Multicat O
    module M = Multicat M

  record MultiFunctor : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    field
      U : Vertical-functor O.disp M.disp
    open Vertical-functor U public
    field
      preserves-inert
        : ∀ {a b a' b'} {f : ⟨ a ⟩→⟨ b ⟩} {f' : O.Hom[ f ] a' b'}
        → f ∈ Inert
        → O.is-cocartesian f f'
        → M.is-cocartesian f (F₁' f')

  unquoteDecl MultiFunctor-up  = declare-record-path MultiFunctor-up (quote MultiFunctor)
  unquoteDecl MultiFunctor-iso  = declare-record-iso MultiFunctor-iso (quote MultiFunctor)

  open MultiFunctor
  MultiFunctor-path
    : {F G : MultiFunctor}
    → (p0 : ∀ {x} → (x' : O.Ob[ x ]) → F .F₀' x' ≡ G .F₀' x')
    → (p1 : ∀ {x y x' y'} {f : Dist.Hom x y} (f' : O.Hom[ f ] x' y')
          → PathP (λ i → M.Hom[ f ] (p0 x' i) (p0 y' i)) (F .F₁' f') (G .F₁' f'))
    → F ≡ G
  MultiFunctor-path p0 p1 = MultiFunctor-up $ Vertical-functor-path p0 p1

IdM : (M : Multicat o ℓ) → MultiFunctor M M
IdM M = record where
  U = Id'
  preserves-inert f i = i

infixr 30 _∘M_
open MultiFunctor
_∘M_
  : ∀ {oe ℓe of ℓf oh ℓh} {M : Multicat oe ℓe} {N : Multicat of ℓf} {S : Multicat oh ℓh}
  → MultiFunctor N S → MultiFunctor M N → MultiFunctor M S
(F' ∘M G') .U = F' .U ∘V G' .U
(F' ∘M G') .preserves-inert i cc = F' .preserves-inert i $ G' .preserves-inert i cc
```

