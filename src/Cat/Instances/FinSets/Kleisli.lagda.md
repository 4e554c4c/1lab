<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import 1Lab.Type.Pointed

open import Cat.Morphism.Factorisation.Orthogonal
open import Cat.Morphism.Factorisation
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Diagram.Product
open import Cat.Morphism.Class
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

import Cat.Morphism

open Functor
```
-->

```agda
module Cat.Instances.FinSets.Kleisli where


private variable
  ℓ : Level
  A : Type ℓ


Fin∙Sets : Precategory lzero lzero
Fin∙Sets .Precategory.Ob = Nat
Fin∙Sets .Precategory.Hom j k = Fin j → Maybe (Fin k)
Fin∙Sets .Precategory.Hom-set _ _ = hlevel 2
Fin∙Sets .Precategory.id = pure
Fin∙Sets .Precategory._∘_ = _<=<_
Fin∙Sets .Precategory.idr f = ext λ _ → refl
Fin∙Sets .Precategory.idl f i x with f x
... | nothing = nothing
... | just x  = just x
Fin∙Sets .Precategory.assoc f g h i x with h x
... | nothing = nothing
... | just x with g x
...   | nothing = nothing
...   | just y = f y

--open Precategory Fin∙Sets
open Cat.Morphism Fin∙Sets


ρ[_] : ∀ {n} → Fin n → Fin n → Maybe (Fin 1)
ρ[ k ] m = ifᵈ (m ≡ᵢ? k) then just 0 else nothing

zero-is-initial : is-initial Fin∙Sets 0
zero-is-initial _ .centre _ = nothing
zero-is-initial _ .paths _ = ext λ ()

zero-is-terminal : is-terminal Fin∙Sets 0
zero-is-terminal n .centre _ = nothing
zero-is-terminal n .paths x = ext λ y → sym $ refute-just (λ ()) (x y)

open is-zero
zero-is-zero : is-zero Fin∙Sets 0
zero-is-zero .has-is-initial = zero-is-initial
zero-is-zero .has-is-terminal = zero-is-terminal

is-inert : ∀ {n m} → (Fin n → Maybe (Fin m)) → Type
is-inert f = ∀ n → is-contr (fibre f (just n))

ρ-inert : ∀ {n k} → is-inert {n} ρ[ k ]
ρ-inert {n} {k} d .centre .fst = k
ρ-inert {n} {k} d .centre .snd with fin-view d
... | zero = refl
ρ-inert {n} {k} d .paths (k' , p) = Σ-prop-path! (sym pf) where
  pf : k' ≡ k
  pf with (k' ≡ᵢ? k)
  pf | yes q = Id≃path.to q
  pf | no ¬q = absurd $ᵢ nothing≠just p


{-
is-inert-is-prop : ∀ {n m} (f : Fin n → Maybe (Fin m)) → is-prop (is-inert f)
is-inert-is-prop {n} {m} f = hlevel 1
-}

instance
  Dec-is-inert : ∀ {n m} {f : Fin n → Maybe (Fin m)} → Dec (is-inert f)
  Dec-is-inert {n} {m} {f} = Dec-Fin-∀ ⦃ Fin-find-unique _ ⦄

inert-inv : ∀ {n m} → (f : Fin n → Maybe (Fin m)) → is-inert f → (Fin m → Fin n)
inert-inv f inert k = inert k .centre .fst

uninv : ∀ {n m} → (f : Fin m → Fin n) → Fin n → Maybe (Fin m)
-- todo use inductive equality here?
uninv f k with Fin-omniscience (λ l → f l ≡ k)
... | inl (k , p , lt) = just k
... | inr ¬p = nothing

uninv-inv : ∀ {n m} → {f : Fin m → Fin n} → ∀ {k x} →  uninv f k ≡ just x → f x ≡ k
uninv-inv {n} {m} {f} {k} {x} p with Fin-omniscience (λ l → f l ≡ k)
... | inl (x' , q , _) = (ap f $ sym $ just-inj p) ∙ q
... | inr ¬p = absurd $ᵢ nothing≠just p

uninv-inert : ∀ {n m} → (f : Fin m → Fin n) → (injective f) → is-inert (uninv f)
uninv-inert f i k .centre .fst = f k
uninv-inert f i k .centre .snd with Fin-omniscience (λ l → f l ≡ f k)
... | inl (k' , p , _) = ap just $ i p
... | inr ¬p = absurd $ᵢ ¬p k refl
uninv-inert f i k .paths (_ , p) = Σ-prop-path! $ uninv-inv p

-- an inductive formulation of `is-just` that doesn't reduce definitionally to ⊤ or ⊥
-- another alternative is something like .jj : So (is-some x)
data is-just' {ℓ : Level} {A : Type ℓ} : Maybe A → Type ℓ where
  jj : {x : A} → is-just' (just x)

instance
  Dec-is-just' : {m : Maybe A} → Dec (is-just' m)
  Dec-is-just' {m = nothing} = no λ ()
  Dec-is-just' {m = just x} = yes jj
  H-Level-is-just' : ∀ {n} {x : Maybe A} → H-Level (is-just' x) (suc n)
  H-Level-is-just' {x = just _} = prop-instance λ { jj jj → refl }
  H-Level-is-just' {x = nothing} = prop-instance λ ()

-- instead of negating the fibre here, we use a slightly more constructive, equivalent definition
is-active : ∀ {n m} → (Fin n → Maybe (Fin m)) → Type
is-active {_} {m} f = ∀ j → is-just' (f j)

never-nothing→active : ∀ {n m} → {f : Fin n → Maybe (Fin m)} → (∀ k → f k ≠ nothing) → is-active f
never-nothing→active {f = f} p j with f j | p j
... | just k  | _ = jj
... | nothing | q = absurd $ᵢ q refl

is-active-is-prop : ∀ {n m} {f : Fin n → Maybe (Fin m)} → is-prop (is-active f)
is-active-is-prop {f = f} p q = hlevel!

Inert : Arrows Fin∙Sets lzero
Inert .arrows = is-inert
Inert .is-tr = hlevel 1

Active : Arrows Fin∙Sets lzero
Active .arrows = is-active
Active .is-tr = is-active-is-prop

module factor {n m} (f : Hom n m) where

  CoKer = Σ[ l ∈ Fin n ] is-just' (f l)

  σ : Fin n → Maybe CoKer
  σ l = (l ,_) <$> Dec→Maybe

  -- likewise we can map through f to `Fin m`. This bit must be active
  π : CoKer → Maybe (Fin m)
  π = f ⊙ fst

  σ-then-π-is-f : ∀ n → (σ n >>= π) ≡ᵢ f n
  σ-then-π-is-f j with holds? $ is-just' (f j)
  ... | yes p = reflᵢ
  ... | no ¬p with f j
  ...   | nothing = reflᵢ
  ...   | just x = absurd $ᵢ ¬p jj

  -- not sure why Listing-prop isn't a class otherwise this is auto
  listing : Listing CoKer
  listing = Listing-Σ ⦃ auto ⦄ ⦃ Listing-prop ⦄
  module listing = Listing listing

  mid = listing.card

  eqv_fin : Fin mid ≃ CoKer
  eqv_fin = listing.listing→fin-equiv
  module eqv_fin = Equiv eqv_fin

  left : Hom n mid
  left = listing.index <∙> σ

  right : Hom mid m
  right = π ⊙ (listing.univ !_)

  left∈L : left ∈ Inert
  left∈L j  = pf where
    prelemma : ∀ {k l p} → σ k ≡ just (l , p) → k ≡ l
    prelemma {k} p with holds? $ is-just' (f k)
    ... | yes a = ap fst $ just-inj p
    ... | no  _ = absurd $ᵢ nothing≠just p

    lemma : (k : CoKer) → is-contr (fibre σ (just k))
    lemma (k , p) .centre .fst = k
    lemma (k , p) .centre .snd with holds? $ is-just' (f k)
    ... | yes a = ap just $ Σ-prop-path! refl
    ... | no ¬a = absurd $ᵢ ¬a p
    lemma (k , p) .paths (x , q) = Σ-prop-path! (sym $ prelemma q)

    pf : is-contr (fibre left (just j))
    pf .centre .fst = lemma (listing.univ ! j) .centre .fst
    pf .centre .snd =
      left ((listing.univ ! j) .fst) ≡⟨ ap (map listing.index) $ lemma (listing.univ ! j) .centre .snd ⟩
      just (listing.index (listing.univ ! j)) ≡⟨ ap just $ eqv_fin.η j ⟩
      just j ∎
    pf .paths (k , p) = Σ-prop-path! $ ap fst $ lemma (listing.univ ! j) .paths $ k , unmap-equiv _ eqv_fin.inverse j p

  right∈R : right ∈ Active
  right∈R j = snd (listing.univ ! j)
{-
never-nothing→active λ k → lemma (eqv_fin.to k) where
    lemma : (k : CoKer) → π k ≠ nothing
    lemma (l , p) pf with f l
    ... | just x = just≠nothing pf
-}

  factors-ext : ∀ n → f n ≡ ((left n) >>= right)
  factors-ext n with holds? $ is-just' (f n)
  ... | yes p = sym $ ap (f ⊙ fst) $ eqv_fin.ε (n , p)
  ... | no ¬p with f n
  ...   | just x = absurd $ᵢ ¬p jj
  ...   | nothing = refl

  factors : f ≡ (left >=> right)
  factors = ext factors-ext


factors : ∀ {n m} (f : Hom n m)
  → Factorisation Fin∙Sets Inert Active f
factors f = record { factor f }

from-just' : (x : Maybe A) → is-just' x → A
from-just' (just a) jj = a

open Cat.Morphism.is-invertible
is-inv→is-just' : ∀ {n m : Nat} → (f : Hom n m) → is-invertible f → ∀ k → is-just' (f k)
is-inv→is-just' f iv k with f k | iv .invr · k
... | nothing | q = absurd $ᵢ nothing≠just q
... | just x | _ = jj

open is-ofs
factor-is-ofs :  is-ofs Fin∙Sets Inert Active
factor-is-ofs .is-ofs.factor = factors
factor-is-ofs .is-iso→in-L f iv n .centre with iv .inv n | iv .invl · n
... | nothing | q = absurd $ᵢ nothing≠just q
... | just k | q = k , q
factor-is-ofs .is-iso→in-L f iv n .paths (a , p) with iv .inv n | iv .invl · n
... | nothing | q = absurd $ᵢ nothing≠just q
... | just k | q = Σ-prop-path! {! !}
factor-is-ofs .L-is-stable f g x x₁ n = {! !}
factor-is-ofs .is-iso→in-R f iv = is-inv→is-just' _ iv
factor-is-ofs .R-is-stable f g x x₁ j = {! !}
factor-is-ofs .L⊥R = {! !}
```
