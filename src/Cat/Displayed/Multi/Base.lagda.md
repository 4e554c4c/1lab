<!--
```agda
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
import Cat.Displayed.Cocartesian
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism
import Cat.Reasoning

import Order.Reasoning
```
-->

```agda
module Cat.Displayed.Multi.Base where
```

# Displayed multicategories {defines=displayed-multicategory}

```agda
open Precategory Δ∙ using (_∘_)
private variable
  o ℓ : Level

record Multicat-over (E : Displayed Δ∙ o ℓ)  : Type (lsuc (o ⊔ ℓ)) where
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
    → Hom[ f ] A B → (i : Fin n) → Hom[ ρ[ i ] ∘ f ] A (B ![ i ])
  _M![_] {A = A} {B = B} {f = f} h k = lift-inert ρ[ k ] (ρ-inert {k = k}) B .lifting ∘' h

  -- this transformation should be an equivalence
  field
    idx-is-eqv : ∀ {m n} {A : Ob[ m ]} {B : Ob[ n ]} → {f : ⟨ m ⟩→⟨ n ⟩} → is-equiv (_M![_] {m} {n} {A} {B} {f})

  -- finally, we can lift vecs to elements of E
    vec→ob : ∀ {n} (C[_] : (Fin n) → Ob) →
      Σ[ C ∈ Ob[ n ] ] ((k : Fin n) → Σ[ f ∈ Hom[ ρ[ k ] ] C C[ k ] ] is-cocartesian ρ[ k ] f)

module _ {ℰ : Displayed Δ∙ o ℓ} {ℱ : Displayed Δ∙ o ℓ} (O : Multicat-over ℰ) (M : Multicat-over ℱ) where
  private
    module O = Multicat-over O
    module M = Multicat-over M

  record MultiFunctorOver : Type (lsuc (o ⊔ ℓ)) where
    field
      U : Displayed-functor Id ℰ ℱ
    open Displayed-functor U public
    field
      preserves-inert
        : ∀ {a b a' b'} {f : ⟨ a ⟩→⟨ b ⟩} {f' : O.Hom[ f ] a' b'}
        → f ∈ Inert
        → O.is-cocartesian f f'
        → M.is-cocartesian f (F₁' f')

record Multicat (o ℓ : Level) : Type (lsuc (o ⊔ ℓ)) where
  field
    ℰ : Displayed Δ∙ o ℓ
    is-multi : Multicat-over ℰ

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

  open Displayed
  to-displayed : Displayed Δ∙ o ℓ
  --to-displayed .Ob[_] 0 = Lift ⊤
  --to-displayed .Ob[_] 1 = Ob
  to-displayed .Ob[_] n = Vec Ob n
  to-displayed .Hom[_] {n} {m} f v v' = ∀ (k : Fin m) → Homl (lookup v <$> preimage-indices f k) (lookup v' k)
  to-displayed .Hom[_]-set {n} {m} f v v' = Π-is-hlevel 2 λ _ → Homl-is-set _ _
  -- do we really want a transp here?
  to-displayed .id' {n} {xs} k = transport (λ j → Homl (lookup xs <$> preimage-id {j = k} (~ j)) (lookup xs k) ) $ id (lookup xs k)
  to-displayed ._∘'_ {a} {b} {c} {xs} {ys} {zs} {f} {g} f' g' k = transport (λ i → Homl (motive₃ i) (lookup zs k)) $ foo module multi-comp where

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
      lookup ys (lookup mid j) ≡˘⟨ {! !} ⟩
      lookup (lookup ys <$> mid) j ∎

    correct-thing : (j : Fin ‖ f ⁻¹ k ‖) → Homl (lookup (lookup xs <<$>> upper) j) (lookup (lookup ys <$> mid) j)
    correct-thing j = transport (λ i → Homl (motive₁ j i) (motive₂ j i)) $ g' (lookup mid j)

    foo : Homl (concat $ lookup xs <<$>> upper .lower) (lookup zs k)
    foo = comp-homl (lookup xs <<$>> upper) (lookup ys <$> mid) (lookup zs k) (λ j → correct-thing j) (f' k)
    -- but we _need_
    -- Homl (lookup xs <$> preimage-indices (f ∘ g) k) (lookup zs k)
    --
    motive₃ : (concat $ lookup xs <<$>> upper .lower) ≡ (lookup xs <$> preimage-indices (f ∘ g) k)
    motive₃ =
      (concat $ lookup xs <<$>> upper .lower)
        ≡⟨⟩
      (concat $ lookup xs <<$>> (tabulate λ j → (preimage-indices g $ lookup mid j)) .lower)
        ≡⟨ {! map-lookup !} ⟩
      lookup xs <$> (concat $ (tabulate λ j → (preimage-indices g $ lookup mid j)) .lower)
        ≡⟨⟩
      lookup xs <$> (concat $ (tabulateℓ λ j → (preimage-indices g $ (preimage-indices f k) ! j)))
        ≡⟨ {! !} ⟩
      lookup xs <$> (concat $ preimage-indices g <$> (tabulateℓ λ j → (preimage-indices f k) ! j))
        ≡⟨ {! !} ⟩
      lookup xs <$> (concat $ preimage-indices g <$> (preimage-indices f k))
        ≡⟨ {! !}  -- this is actually the important theorem
         ⟩
      lookup xs <$> preimage-indices (f ∘ g) k
        ∎

  to-displayed .idr' {a} {b} {x = xs} {ys} {f} f' i k = comp (λ j →
      Homl (multi-comp.motive₃ {a} {a} {b} {xs} {xs} {ys} {f} {Δ-id} 
        f' (λ k' → transport (λ j' → Homl (lookup xs <$> preimage-id {a} {k'} (~ j')) (lookup xs k')) (id (lookup {o} xs k'))) k (j)) (lookup ys k)
    ) (∂ i) λ where
    j (i = i0) → {! !}
    j (i = i1) → {! !}
    j (j = i0) → {! idr !}
  to-displayed .idr' {x = xs} {ys} f' = ext λ k → {! !}
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
```

