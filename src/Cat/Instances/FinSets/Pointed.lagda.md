<!--
```agda
open import 1Lab.Type.Pointed

open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Diagram.Product
open import Cat.Diagram.Zero
open import Cat.Functor.Base
open import Cat.Prelude

open import Data.Maybe.Properties
open import Data.Fin.Closure
open import Data.Maybe.Base
open import Data.Dec.Base
open import Data.Sum.Base
open import Data.List
open import Data.Fin
open import Data.Irr
open import Data.Nat

open import Meta.Idiom

open Functor
```
-->

```agda
module Cat.Instances.FinSets.Pointed where

Fin∙ : Nat → Type∙ lzero
Fin∙ n = Fin (suc n) , 0

inj : ∀ {n} → Fin n → ⌞ Fin∙ n ⌟
inj = fsuc


instance
  Extensional∙ : ∀ {n m} → Extensional (Fin∙ n →∙ Fin∙ m) lzero
  Extensional∙ .Pathᵉ f g = ∀ n → f · (inj n) ≡ g · (inj n)
  Extensional∙ .reflᵉ f n = refl
  Extensional∙ .idsᵉ .to-path {f} {g} p = Σ-prop-path! (ext p') where
    p' : ∀ k → f · k ≡ g · k
    p' k with fin-view k
    ... | zero = f .snd ∙ sym (g .snd)
    ... | suc k = p k
  Extensional∙ .idsᵉ .to-path-over {f} {g} p = is-prop→pathp (λ i → hlevel 1) _ _



private module _ where
  lemm : ∀ {n} → Fin∙ n ≃∙ (Maybe (Fin n), nothing)
  lemm .fst .fst k with fin-view k
  ... | zero  = nothing
  ... | suc k = just k
  lemm .fst .snd = is-iso→is-equiv i where
    open is-iso
    i : is-iso _
    i .from nothing  = 0
    i .from (just x) = fsuc x
    i .rinv nothing  = refl
    i .rinv (just _) = refl
    i .linv k with fin-view k
    ... | zero = refl
    ... | suc _ = refl
  lemm .snd = refl

-- a fonction is 'inert' if it's an equivalence away from 0
is-inert : ∀ {n m} → (Fin∙ n →∙ Fin∙ m) → Type
is-inert (f , _) = ∀ n → is-contr (fibre f (inj n))

inert-inv : ∀ {n m} → (f : Fin∙ n →∙ Fin∙ m) → is-inert f → (Fin m → Fin n)
inert-inv f inert k with c ← inert k with fin-view (c .centre .fst)
... | zero = absurd $ᵢ fzero≠fsuc $ sym p ∙ q where
  p : f · 0 ≡ 0
  p = f .snd
  q : f · 0 ≡ fsuc k
  q = c .centre .snd
... | suc i = i

is-active : ∀ {n m} → (Fin∙ n →∙ Fin∙ m) → Type
is-active (f , _) = is-contr (fibre f 0)


ρ[_] : ∀ {n} → Fin n → Fin∙ n →∙ Fin∙ 1
ρ[ k ] .fst m = ifᵈ (m ≡ᵢ? inj k) then 1 else 0
ρ[ k ] .snd = refl

ρ-inert : ∀ {n k} → is-inert {n} ρ[ k ]
ρ-inert {n} {k} d .centre .fst = inj k
ρ-inert {n} {k} d .centre .snd with fin-view d
... | zero = refl
ρ-inert {n} {k} d .paths (k' , p) = Σ-prop-path! (sym pf) where
  pf : k' ≡ inj k
  pf with (k' ≡ᵢ? inj k)
  pf | yes q = Id≃path.to q
  pf | no ¬q = absurd $ᵢ fzero≠fsuc p

Fin∙Sets : Precategory lzero lzero
Fin∙Sets .Precategory.Ob = Nat
Fin∙Sets .Precategory.Hom j k = Fin∙ j →∙ Fin∙ k
Fin∙Sets .Precategory.Hom-set _ _ = hlevel 2
Fin∙Sets .Precategory.id = id∙
Fin∙Sets .Precategory._∘_ = _∘∙_
Fin∙Sets .Precategory.idr = ∘∙-idr
Fin∙Sets .Precategory.idl = ∘∙-idl
Fin∙Sets .Precategory.assoc = ∘∙-assoc


zero-is-initial : is-initial Fin∙Sets 0
zero-is-initial _ .centre .fst _ = 0
zero-is-initial _ .centre .snd = refl
zero-is-initial _ .paths _ = ext λ ()

zero-is-terminal : is-terminal Fin∙Sets 0
zero-is-terminal n = hlevel 0

open is-zero
zero-is-zero : is-zero Fin∙Sets 0
zero-is-zero .has-is-initial = zero-is-initial
zero-is-zero .has-is-terminal = zero-is-terminal
```
