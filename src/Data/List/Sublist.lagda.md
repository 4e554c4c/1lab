<!--
```agda
open import 1Lab.Prelude

open import Data.List.Membership
open import Data.List.Base
open import Data.Dec.Base
open import Data.Sum.Base
open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Top
open import Order.Base
open import Order.Lattice
```
-->

```agda
module Data.List.Sublist {ℓ} {A : Type ℓ} where
```

<!--
```agda
private variable
  ℓ' : Level
  x y : A
  xs ys : List A
```
-->

```agda
data Sublist  : List A → Type ℓ where
  []S     : Sublist []
  chooseS : ∀ x → Sublist xs → Sublist (x ∷ xs)
  skipS   : ∀ x → Sublist xs → Sublist (x ∷ xs)

data _≤SL_ : Sublist xs → Sublist xs → Type ℓ where
  zleS : ∀ {s} → []S ≤SL s
  clcS : {s s' : Sublist xs} → s ≤SL s' → chooseS x s ≤SL chooseS x s'
  slsS : {s s' : Sublist xs} → s ≤SL s' → skipS x s ≤SL skipS x s'
  slcS : {s s' : Sublist xs} → s ≤SL s' → skipS x s ≤SL chooseS x s'

≤SL-is-prop : {s s' : Sublist xs} → is-prop $ s ≤SL s'
≤SL-is-prop zleS zleS = refl
≤SL-is-prop (clcS p) (clcS q) = ap clcS $ ≤SL-is-prop p q
≤SL-is-prop (slsS p) (slsS q) = ap slsS $ ≤SL-is-prop p q
≤SL-is-prop (slcS p) (slcS q) = ap slcS $ ≤SL-is-prop p q

instance
  H-Level-≤SL : ∀ {xs : List A} {s s' : Sublist xs} {n} → H-Level (s ≤SL s') (suc n)
  H-Level-≤SL = prop-instance ≤SL-is-prop

≤SL-refl : {s : Sublist xs} → s ≤SL s
≤SL-refl {s = []S} =  zleS
≤SL-refl {s = chooseS x s} = clcS ≤SL-refl
≤SL-refl {s = skipS x s} = slsS ≤SL-refl

≤SL-trans : {s t r : Sublist xs} → s ≤SL t → t ≤SL r → s ≤SL r
≤SL-trans zleS zleS = zleS
≤SL-trans (slsS p) (slsS q) = slsS $ ≤SL-trans p q
≤SL-trans (slsS p) (slcS q) = slcS $ ≤SL-trans p q
≤SL-trans (slcS p) (clcS q) = slcS $ ≤SL-trans p q
≤SL-trans (clcS p) (clcS q) = clcS $ ≤SL-trans p q

≤SL-antisym : {s s' : Sublist xs} → s ≤SL s' → s' ≤SL s → s ≡ s'
≤SL-antisym zleS zleS =  refl
≤SL-antisym (clcS p) (clcS q) = ap (chooseS _) $ ≤SL-antisym p q
≤SL-antisym (slsS p) (slsS q) = ap (skipS _) $ ≤SL-antisym p q

--open Poset
Sublist-poset : (xs : List A) → Poset ℓ ℓ
Sublist-poset xs = record where
    Ob        = Sublist xs
    _≤_       = _≤SL_
    ≤-thin    = ≤SL-is-prop
    ≤-refl    = ≤SL-refl
    ≤-trans   = ≤SL-trans
    ≤-antisym = ≤SL-antisym

module Sublist-poset {xs} = Poset (Sublist-poset xs)

instance
  H-Level-Sublist : ∀ {n} → H-Level (Sublist xs) (2 + n)
  H-Level-Sublist = basic-instance 2 Sublist-poset.Ob-is-set

every : Sublist xs
every {[]} = []S
every {x ∷ xs}  = chooseS x every


empty : Sublist xs
empty {[]} = []S
empty {x ∷ xs} = skipS x empty

private module Sublist-lattice where
  _∩_     : Sublist xs → Sublist xs → Sublist xs
  []S ∩ []S               = []S
  chooseS x p ∩ chooseS x q = chooseS x (p ∩ q)
  chooseS x p ∩ skipS x q = skipS x (p ∩ q)
  skipS x p ∩ chooseS x q = skipS x (p ∩ q)
  skipS x p ∩ skipS x q   = skipS x (p ∩ q)

  open is-meet
  open is-join
  ∩-meets : ∀ x y → is-meet (Sublist-poset xs) x y (x ∩ y)
  ∩-meets []S []S .meet≤l = zleS
  ∩-meets (chooseS x s) (chooseS x' t) .meet≤l = clcS $ ∩-meets s t .meet≤l
  ∩-meets (chooseS x s) (skipS x t) .meet≤l = slcS $ ∩-meets s t .meet≤l
  ∩-meets (skipS x s) (chooseS x t) .meet≤l = slsS $ ∩-meets s t .meet≤l
  ∩-meets (skipS x s) (skipS x t) .meet≤l = slsS $ ∩-meets s t .meet≤l

  ∩-meets []S []S .meet≤r = zleS
  ∩-meets (chooseS x s) (chooseS x₁ t) .meet≤r = clcS $ ∩-meets s t .meet≤r
  ∩-meets (chooseS x s) (skipS x₁ t) .meet≤r = slsS $ ∩-meets s t .meet≤r
  ∩-meets (skipS x s) (chooseS x₁ t) .meet≤r = slcS $ ∩-meets s t .meet≤r
  ∩-meets (skipS x s) (skipS x₁ t) .meet≤r = slsS $ ∩-meets s t .meet≤r

  ∩-meets s t .greatest r zleS zleS = zleS
  ∩-meets s t .greatest r (clcS p) (clcS q) = clcS $ ∩-meets _ _ .greatest _ p q
  ∩-meets s t .greatest r (slsS p) (slsS q) = slsS $ ∩-meets _ _ .greatest _ p q
  ∩-meets s t .greatest r (slsS p) (slcS q) = slsS $ ∩-meets _ _ .greatest _ p q
  ∩-meets s t .greatest r (slcS p) (slsS q) = slsS $ ∩-meets _ _ .greatest _ p q
  ∩-meets s t .greatest r (slcS p) (slcS q) = slcS $ ∩-meets _ _ .greatest _ p q

  _∪_     : Sublist xs → Sublist xs → Sublist xs
  []S ∪ []S = []S
  chooseS x s ∪ chooseS x t = chooseS x (s ∪ t)
  chooseS x s ∪ skipS x t = chooseS x (s ∪ t)
  skipS x s ∪ chooseS x t = chooseS x (s ∪ t)
  skipS x s ∪ skipS x t =  skipS x (s ∪ t)

  ∪-joins : ∀ x y → is-join (Sublist-poset xs) x y (x ∪ y)
  ∪-joins []S []S .l≤join = zleS
  ∪-joins (chooseS x s) (chooseS x t) .l≤join = clcS $ ∪-joins _ _ .l≤join
  ∪-joins (chooseS x s) (skipS x t) .l≤join = clcS $ ∪-joins _ _ .l≤join
  ∪-joins (skipS x s) (chooseS x t) .l≤join = slcS $ ∪-joins _ _ .l≤join
  ∪-joins (skipS x s) (skipS x t) .l≤join = slsS $ ∪-joins _ _ .l≤join

  ∪-joins []S []S .r≤join = zleS
  ∪-joins (chooseS x s) (chooseS x t) .r≤join = clcS $ ∪-joins _ _ .r≤join
  ∪-joins (skipS x s) (chooseS x t) .r≤join = clcS $ ∪-joins _ _ .r≤join
  ∪-joins (chooseS x s) (skipS x t) .r≤join = slcS $ ∪-joins _ _ .r≤join
  ∪-joins (skipS x s) (skipS x t) .r≤join = slsS $ ∪-joins _ _ .r≤join

  ∪-joins s t .least r zleS zleS = zleS
  ∪-joins s t .least r (clcS p) (clcS q) = clcS $ ∪-joins _ _ .least _ p q
  ∪-joins s t .least r (clcS p) (slcS q) = clcS $ ∪-joins _ _ .least _ p q
  ∪-joins s t .least r (slcS p) (clcS q) = clcS $ ∪-joins _ _ .least _ p q
  ∪-joins s t .least r (slcS p) (slcS q) = slcS $ ∪-joins _ _ .least _ p q
  ∪-joins s t .least r (slsS p) (slsS q) = slsS $ ∪-joins _ _ .least _ p q

  open Top renaming (has-top to ht)
  has-top : Top (Sublist-poset xs)
  has-top .top = every
  has-top .ht []S = zleS
  has-top .ht (chooseS x s) = clcS $ has-top .ht _
  has-top .ht (skipS x s) = slcS $ has-top .ht _


  open Bottom renaming (has-bottom to hb)
  has-bottom : Bottom (Sublist-poset xs)
  has-bottom .bot = empty
  has-bottom .hb []S = zleS
  has-bottom .hb (chooseS x s) = slcS $ has-bottom .hb _
  has-bottom .hb (skipS x s) = slsS $ has-bottom .hb _

Sublist-lattice : is-lattice (Sublist-poset xs)
Sublist-lattice = record { Sublist-lattice }


sublist : (xs : List A) → Sublist xs → List A
sublist xs []S = []
sublist (x ∷ xs) (chooseS x s) = x ∷ sublist xs s
sublist (x ∷ xs) (skipS x s) = sublist xs s


subSublist : (s : Sublist xs) → Sublist (sublist xs s) → Sublist xs
subSublist []S []S = []S
subSublist (chooseS x s) (chooseS x s') = chooseS x $ subSublist s s'
subSublist (chooseS x s) (skipS x s') = skipS x $ subSublist s s'
subSublist (skipS x s) s' = skipS x $ subSublist s s'
```
