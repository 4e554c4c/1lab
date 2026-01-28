<!--
```agda
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Universe
open import 1Lab.HLevel.Closure
open import 1Lab.Type.Sigma
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
open import 1Lab.Membership
open import 1Lab.Underlying

open import Data.List.Base
open import Data.Dec.Base
open import Data.Fin.Base
open import Data.Nat.Base hiding (_<_)
open import Data.Sum.Base
open import Data.Id.Base
open import Data.Bool

open import Meta.Foldable
open import Meta.Idiom
```
-->

```agda
module Data.List.Sorted where
```

# sort'd list's

```agda
record is-sorted {ℓa ℓr} {A : Type ℓa} (R : A → A → Type ℓr) (xs : List A) : Type ℓr where
  constructor sorting
  field
    sorted : ∀ (i j : Fin (length xs)) → i < j → R (xs ! i) (xs ! j)
```

<!--
```agda

open is-sorted

private variable
  ℓa ℓr : Level
  A : Type ℓa
  R : A → A → Type ℓr
  x : A
  xs : List A
```
-->

```agda

[]-sorted : is-sorted R []
[]-sorted .sorted ()

∷-sorted : ∀ (x : A) (xs : List A) → (∀ (i : Fin (length xs)) → R x (xs ! i)) → is-sorted R xs → is-sorted R (x ∷ xs)
∷-sorted x xs r xs-sorted .sorted i j i<j with fin-view i | fin-view j
... | zero | suc j = r j
... | suc i | suc j = xs-sorted .sorted i j (≤-peel i<j)

tail-sorted : is-sorted R (x ∷ xs) → is-sorted R xs
tail-sorted (sorting r) = sorting $ λ i j p → r (fsuc i) (fsuc j) (s≤s p)

filter-subset : (P : A → Type ℓr) (p : A → Bool) → (∀ i → (xs ! i) ∈ P) → ∀ j → (filter p xs ! j) ∈ P
filter-subset {xs = x ∷ xs} P p mem j with p x
... | false = filter-subset P p (mem ∘ fsuc) j
... | true with fin-view j
...   | zero = mem fzero
...   | suc i = filter-subset P p (mem ∘ fsuc) i

filter-sorted : (xs : List A) (p : A → Bool) → is-sorted R xs → is-sorted R (filter p xs)
filter-sorted [] p xs-sorted = []-sorted
filter-sorted {R = R} (x ∷ xs) p xs-sorted@(sorting r) with p x
... | false = filter-sorted xs p $ tail-sorted xs-sorted
... | true = ∷-sorted x (filter p xs) (filter-subset (R x) p λ i → r fzero (fsuc i) (s≤s 0≤x)) $ filter-sorted xs p $ tail-sorted xs-sorted

```
