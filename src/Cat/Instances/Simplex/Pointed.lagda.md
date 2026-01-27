<!--
```agda
--open import Data.Nat
--open import Cat.Instances.FinSets.Pointed
open import 1Lab.Type.Pointed

open import Cat.Instances.Simplex
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Diagram.Product
open import Cat.Diagram.Zero
open import Cat.Functor.Base
open import Cat.Prelude

open import Data.Fin.Closure
open import Data.Maybe.Base
open import Data.Nat.Order
open import Data.Dec.Base
open import Data.Sum.Base
open import Data.Fin
open import Data.Irr

open import Meta.Idiom

open Functor
```
-->

```agda
module Cat.Instances.Simplex.Pointed where

module _ {n : Nat} where
  data _≲_ : Maybe (Fin n) → Maybe (Fin n) → Type where
    n≲n : nothing ≲ nothing
    n≲j : ∀ {x} → nothing ≲ just x
    j≲n : ∀ {x} → just x ≲ nothing
    j≲j : ∀ {x y} → x ≤ y → just x ≲ just y

  ≲-is-prop : ∀ {x y} → is-prop (x ≲ y)
  ≲-is-prop n≲n     n≲n     = refl
  ≲-is-prop n≲j     n≲j     = refl
  ≲-is-prop j≲n     j≲n     = refl
  ≲-is-prop (j≲j p) (j≲j q) = ap j≲j (hlevel 1 p q)

  instance
    H-Level-≲ : ∀ {m x y} → H-Level (x ≲ y) (suc m)
    H-Level-≲ = prop-instance ≲-is-prop

  n≲x : ∀ {x} → nothing ≲ x
  n≲x {nothing} = n≲n
  n≲x {just x} = n≲j

  x≲n : ∀ {x} → x ≲ nothing
  x≲n {nothing} = n≲n
  x≲n {just x} = j≲n

record _Δ∙→_ (n m : Nat) : Type where
  constructor sasc
  field
    map       : Fin (suc n) → Maybe (Fin (suc m))
    ascending : (x y : Fin (suc n)) → x ≤ y → map x ≲ map y

open _Δ∙→_

_Δ∙∘_  : ∀{n m k} (f : m Δ∙→ k) (g : n Δ∙→ m) → n Δ∙→ k
(f Δ∙∘ g) .map = f .map <=< g .map
(f Δ∙∘ g) .ascending x y p with g .map x | g .map y | g .ascending x y p
... | nothing | _       | _     = n≲x
... | just _  | nothing | _     = x≲n
... | just x  | just y  | j≲j q = f .ascending x y q

-- a function is 'inert' if it's an equivalence to its defined domain
is-inert : ∀ {n m} → (n Δ∙→ m) → Type
is-inert (sasc f _) = ∀ x → is-contr (fibre f (just x))

ρ[_] : ∀ {n} → Fin (suc n) → n Δ∙→ 1
ρ[ k ] .map x = ifᵈ (x ≡ᵢ? k) then just 0 else nothing
ρ[ k ] .ascending x y p with (x ≡ᵢ? k) | (y ≡ᵢ? k)
... | no ¬a | q = n≲x
... | yes a | yes b = j≲j 0≤x
... | yes a | no ¬b = x≲n

inert-inv : ∀ {n m} → (f : n Δ∙→ m) → is-inert f → (Fin (suc m) → Fin n)
inert-inv f inert k with c ← inert k with fin-view (c .centre .fst)
... | zero = {! c .centre .snd !}
  --absurd $ᵢ fzero≠fsuc $ sym p ∙ q where
  --p : f · 0 ≡ 0
  --p = f .snd
  --q : f · 0 ≡ fsuc k
  --q = c .centre .snd
... | suc i = i

{-
-- a fonction is 'inert' if it's an equivalence away from 0
is-inert : ∀ {n m} → (Fin∙ n →∙ Fin∙ m) → Type
is-inert (f , _) = ∀ n → is-contr (fibre f (inj n))


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


--data e : Type → Type where


--Δ∙ : Nat → Type∙ lzero
--Δ∙ n = Fin∙ (suc n)

-}
```
