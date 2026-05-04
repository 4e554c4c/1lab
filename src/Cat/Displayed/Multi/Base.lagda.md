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

import Cat.Displayed.IsoFibration
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
  open Cat.Displayed.IsoFibration E
  open Cocartesian-lift

  module lift-inert {m n} (f : ⟨ m ⟩→⟨ n ⟩)(f-inert : is-inert f) C
    = Cocartesian-lift (lift-inert f f-inert C)

  module lift-ρ {n} (C : Ob[ n ]) k = lift-inert ρ[ k ] (ρ-inert {k = k}) C

  Ob : Type o
  Ob = Ob[ 1 ]


  infixl 50 _![_] _M![_] _!![_]
  -- A : Ob[ m ] is a "vec" of colors
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
    vec→ob : ∀ {n} (C[_] : (Fin n) → Ob) → Ob[ n ]

    vec-proj : ∀ {n} (C[_] : (Fin n) → Ob) → (k : Fin n) → Cocartesian-morphism ρ[ k ] (vec→ob C[_]) C[ k ]

  module vec-proj {n} (C[_] : (Fin n) → Ob) (k : Fin n)
    = Cocartesian-morphism (vec-proj C[_] k)

  vec→hom
    : ∀ {m n} {A : Ob[ m ]} {B : Ob[ n ]} → {f : ⟨ m ⟩→⟨ n ⟩}
    → ((i : Fin n) → Hom[ ρ[ i ] ∘ f ] A (B ![ i ])) → Hom[ f ] A B
  vec→hom = equiv→inverse idx-is-eqv

  open Cocartesian-morphism

  vec→ob!≅vec : ∀ {n} (C[_] : (Fin n) → Ob) → ∀ i →
    vec→ob C[_] ![ i ] ≅↓ C[ i ]
  vec→ob!≅vec C[_] i = cocartesian-codomain-unique
      (lift-ρ.cocartesian _ i)
      (vec-proj C[_] i .cocartesian)

  module vec→ob!≅vec {n} C i = _≅[_]_ (vec→ob!≅vec {n} C i)

  _!⟨_⟩[_] : ∀ {m n} {A : Ob[ m ]} {B : Ob[ n ]} → {f : ⟨ m ⟩→⟨ n ⟩}
    → Hom[ f ] A B → (f-inert : is-inert f) → (i : Fin n) → Hom[ id ] (A ![ inert-inv {f = f} f-inert i ]) (B ![ i ])
  _!⟨_⟩[_] {A = A} {B = B} {f = f} h f-inert k = lift-ρ.universal' A (inert-inv {f = f} f-inert k) (Dist.idl _ ∙ (sym $ inert-ρ f-inert)) $ h M![ k ]

  _!![_] : ∀ {n} {A : Ob[ n ]} {B : Ob[ n ]}
    → Hom[ id ] A B → (i : Fin n) → Hom[ id ] (A ![ i ]) (B ![ i ])
  _!![_] {A = A} {B = B} h k = lift-ρ.universal' A k (idl _) $ h M![ k ]


  vec→hom'
    : ∀ {n} {A : Ob[ n ]} {B : Ob[ n ]}
    → ((i : Fin n) → Hom[ id ] (A ![ i ]) (B ![ i ])) → Hom[ id ] A B
  vec→hom' {A = A} {B} fs = vec→hom λ i → hom[ id-comm-sym ] $ fs i ∘' lift-ρ.lifting A i


  vec-idx' : ∀ {n} {A : Ob[ n ]} {B : Ob[ n ]}
    → (fs : (i : Fin n) → Hom[ id ] (A ![ i ]) (B ![ i ])) → ∀ k → (vec→hom' fs) !![ k ] ≡ fs k
  vec-idx' {A = A} {B} fs k = sym $ lift-ρ.uniquep A k id-comm-sym _ _ _ $ begin[]
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

--instance
--  Underlying-Multicat : Underlying (Multicat o ℓ)
--  Underlying-Multicat = record { ⌞_⌟ = ⌞_⌟ ⊙ Multicat.disp }

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

module _
  {oe ℓe of ℓf oh ℓh}
  {M : Multicat oe ℓe}
  {N : Multicat of ℓf}
  {S : Multicat oh ℓh}
  where
  --open Displayed-functor
  --open is-fibred-functor

  infixr 30 _∘M_
  open MultiFunctor
  _∘M_ : MultiFunctor N S → MultiFunctor M N → MultiFunctor M S
  (F' ∘M G') .U = F' .U ∘V G' .U
  (F' ∘M G') .preserves-inert i cc = F' .preserves-inert i $ G' .preserves-inert i cc


record make-multicat (o ℓ : Level) : Type (lsuc (o ⊔ ℓ)) where
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

    idl
      : ∀ {xs y} {h : Homl xs y} →
      PathP (λ i → Homl (singleton-bind xs i) y)
      (comp-homl (singleton <$> vec xs) (vec xs) y
        (λ j → transport (λ i → Homl (map-lookup singleton (vec xs) j (~ i)) (xs ! j)) $ id (xs ! j ))
        h)
      h

    idr
      : ∀ {xs y} {h : Homl xs y} →
      PathP (λ i → Homl (++-idr xs i) y)
        (comp-homl [ xs ] [ y ] y (const→fin1 h) (id y))
        h
{-

  open Displayed
  to-displayed : Displayed Dist o ℓ
  --to-displayed .Ob[_] 0 = Lift ⊤
  --to-displayed .Ob[_] 1 = Ob
  to-displayed .Ob[_] n = Vec Ob n
  to-displayed .Hom[_] {n} {m} f v v' = ∀ (k : Fin m) → Homl (lookup v <$> preimage-indices f k) (lookup v' k)
  to-displayed .Hom[_]-set {n} {m} f v v' = Π-is-hlevel 2 λ _ → Homl-is-set _ _
  -- do we really want a transp here?
  to-displayed .id' {n} {xs} k = transport (λ j → Homl (lookup xs <$> preimage-id {j = k} (~ j)) (lookup xs k) ) $ id (lookup xs k)
  to-displayed ._∘'_ {a} {b} {c} {xs} {ys} {zs} {f} {g} f' g' k = transport (λ i → Homl (motive₃ i) (lookup zs k)) $ foo
    module multi-comp where

    -- n = ‖ f ⁻¹ k ‖

    mid : Vec (Fin b) ‖ f ⁻¹ k ‖
    mid = vec (preimage-indices f k)


    upper : Vec (List $ Fin a) ‖ f ⁻¹ k ‖
    upper = tabulate λ j → preimage-indices g $ lookup mid j

    --foo : Homl (concat $ _) _
    -- NEED Homl (lookup (lookup xs <<$>> upper) j) (lookup (lookup ys <$> mid) j)
    -- lookup-map ~= Homl (lookup (lookup xs <<$>> upper) j) (lookup ys (lookup mid j))
    -- lookup-map ~= Homl ((lookup xs <$> lookup upper j) (lookup ys (lookup mid j))
    -- lookup-tab ~= Homl ((lookup xs <$> preimage-indices g (lookup mid j)) (lookup ys (lookup mid j))
    -- which we have!!
    g-thing : (j : Fin ‖ f ⁻¹ k ‖) → Homl (lookup xs <$> preimage-indices g (lookup mid j)) (lookup ys (lookup mid j))
    g-thing j = g' (lookup mid j)

    motive₁ : (j : Fin ‖ f ⁻¹ k ‖) → (lookup xs <$> preimage-indices g (lookup mid j)) ≡ lookup (lookup xs <<$>> upper) j
    motive₁ j =
      (lookup xs <$> preimage-indices g (lookup mid j))
        ≡˘⟨ ap (map $ lookup xs) $ lookup-tabulate _ j ⟩
      (lookup xs) <$> (lookup upper j)
        ≡˘⟨ map-lookup (map $ lookup xs) upper j ⟩
      lookup (map (lookup xs) <$> upper) j
        ≡⟨⟩
      lookup (lookup xs <<$>> upper) j ∎

    motive₂ : ∀ j → lookup ys (lookup mid j) ≡ lookup (lookup ys <$> mid) j
    motive₂ j =
      lookup ys (lookup mid j) ≡˘⟨ map-lookup (lookup ys) mid j ⟩
      lookup (lookup ys <$> mid) j ∎

    correct-thing : (j : Fin ‖ f ⁻¹ k ‖) → Homl (lookup (lookup xs <<$>> upper) j) (lookup (lookup ys <$> mid) j)
    correct-thing j = transport (λ i → Homl (motive₁ j i) (motive₂ j i)) $ g' (lookup mid j)

    foo : Homl (concat $ lookup xs <<$>> upper .lower) (lookup zs k)
    foo = comp-homl (lookup xs <<$>> upper) (lookup ys <$> mid) (lookup zs k) (λ j → correct-thing j) (f' k)
    -- but we _need_
    -- Homl (lookup xs <$> preimage-indices (f ∘ g) k) (lookup zs k)
    --
    motive₃ : (concat $ lookup xs <<$>> upper .lower) ≡ (lookup xs <$> preimage-indices (f Dist.∘ g) k)
    motive₃ =
      (concat $ lookup xs <<$>> upper .lower)
        ≡⟨⟩
      (concat $ lookup xs <<$>> (tabulate λ j → (preimage-indices g $ lookup mid j)) .lower)
        ≡⟨ concat-mapp {xs = tabulateℓ λ j → (preimage-indices g $ (preimage-indices f k) ! j)} (lookup xs) ⟩
      lookup xs <$> (concat $ (tabulate λ j → (preimage-indices g $ lookup mid j)) .lower)
        ≡⟨⟩
      lookup xs <$> (concat $ (tabulateℓ λ j → (preimage-indices g $ (preimage-indices f k) ! j)))
        ≡˘⟨ ap (λ c → lookup xs <$> (concat c)) $ map-tabulate (preimage-indices g) (λ j → (preimage-indices f k) ! j) ⟩
      lookup xs <$> (concat $ preimage-indices g <$> (tabulateℓ λ j → (preimage-indices f k) ! j))
        ≡⟨ ap (λ c → Map-List .map (lookup xs) (concat $ Map-List .map (preimage-indices g) c)) $ tabulate-! {xs = preimage-indices f k} ⟩
      lookup xs <$> (concat $ preimage-indices g <$> (preimage-indices f k))
        ≡⟨ ap (λ l → Map-List .map (lookup xs) l) {! !}  -- this is actually the important theorem
         ⟩
      lookup xs <$> preimage-indices (f Dist.∘ g) k
        ∎

  to-displayed .idr' {a} {b} {x = xs} {ys} {f} f' = {! !}
{-
  to-displayed .idr' {a} {b} {x = xs} {ys} {f} f' i k = comp (λ j →
      Homl (multi-comp.motive₃ {a} {a} {b} {xs} {xs} {ys} {f} {Δ-id}
        f' (λ k' → transport (λ j' → Homl (lookup xs <$> preimage-id {a} {k'} (~ j')) (lookup xs k')) (id (lookup {o} xs k'))) k (j)) (lookup ys k)
    ) (∂ i) λ where
    j (i = i0) → transp (λ i₁ → Homl (multi-comp.motive₃ {a} {a} {b} {xs} {xs} {ys} {f} {Δ-id} f' (λ k₁ → transport (λ j₁ → Homl (lookup xs <$> preimage-id (~ j₁)) (lookup xs k₁)) (id (lookup xs k₁))) k i₁) (lookup ys k)) j (multi-comp.foo f' (λ k₁ → transport (λ j₁ → Homl (lookup xs <$> preimage-id (~ j₁)) (lookup xs k₁)) (id (lookup xs k₁))) k)
    j (i = i1) → {! !}
    j (j = i0) → {! !}
  --to-displayed .idr' {x = xs} {ys} f' = ext λ k → {! !}
-}
  to-displayed .idl' f' = {! !}
  to-displayed .assoc' f' g' h' = {! !}
  to-displayed .hom[_] {x = xs} {ys} p f k = transport (λ j → Homl (lookup xs <$> preimage-indices (p j) k) (lookup ys k)) $ f k
  to-displayed .coh[_] {x = xs} {ys} p f i k = transp (λ j → Homl (lookup xs <$> preimage-indices (p (i ∧ j)) k) (lookup ys k)) (~ i) $ f k
  --to-operad : Operad

  open Cat.Displayed.Cocartesian to-displayed public
  open Cat.Displayed.IsoFibration to-displayed

  module _ {m n} (f : ⟨ m ⟩→⟨ n ⟩) (inert : is-inert f) (v : Vec Ob m) where
    open Cocartesian-lift
    open is-cocartesian

    inv : Fin n → Fin m
    inv = inert-inv f inert

    theorem : ∀ k → Path (List $ Fin m) (preimage-indices f k) (singleton $ inv k)
    theorem k = {! !}


    lift-inert : Cocartesian-lift f v
    lift-inert .y' = tabulate λ j → lookup v (inv j)
    lift-inert .lifting k = transport (λ i → Homl (lookup v <$> theorem k (~ i)) (lookup-tabulate (λ z → lookup v (inv z)) k (~ i))) (id $ lookup v $ inv k)
      -- want Homl (lookup v <$> preimage-indices f k) (lookup (tabulate (λ j → lookup v (inv j))) k)
      -- == Homl (lookup v <$> preimage-indices f k) (lookup v (inv k))
      -- ~= Homl (lookup v <$> [ inv k ]) (lookup v (inv k))
      -- <: id {inv k}
    lift-inert .cocartesian .universal m fs k = {! !}
      -- want Goal: Homl (lookup (tabulate (λ j → lookup v (inv j))) <$>  preimage-indices m k) (lookup u' k)
    lift-inert .cocartesian .commutes m h' = {! !}
    lift-inert .cocartesian .unique m' x = {! !}
-}
```

