<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Universe
open import 1Lab.HLevel.Closure
--open import 1Lab.Type.Sigma
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type hiding (Σ-syntax)
open import 1Lab.Membership
open import 1Lab.Underlying

open import Data.List.Base
open import Data.List.Properties
open import Data.List.Membership
open import Data.Dec.Base
open import Data.Fin.Base
open import Data.Nat.Base renaming (_<_ to _<n_ ; _≤_ to _≤n_)
open import Data.Nat.Order
open import Data.Nat.Properties
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
... | true = ∷-sorted x (filter p xs) (filter-subset (R x) p λ i → r fzero (fsuc i) 1≤s) $ filter-sorted xs p $ tail-sorted xs-sorted

mem→rel :  ∀ {x y} {xs : List A} → is-sorted R (x ∷ xs) → (y ∈ xs) → R x y
mem→rel {x = x} {y} (sorting r) mem with member→lookup mem
... | j , reflᵢ = r 0 (fsuc j) 1≤s

---member-++-view
---  : ∀ {ℓ} {A : Type ℓ} {x : A} (xs : List A) (ys : List A)
---  → (p : x ∈ₗ (xs ++ ys)) → Member-++-view x xs ys p
---member-++-view []       _ p         = inr (p , refl)
---member-++-view (x ∷ xs) _ (here p)  = inl (here p , refl)
---member-++-view (x ∷ xs) _ (there p) with member-++-view xs _ p
---... | inl (p , q) = inl $ there p , ap there q
---... | inr (p , q) = inr $ p , ap there q

concat-index
  : ∀ {A : Type ℓa} (xxs : List $ List A) i
  → Σ[ j ∈ Fin (length xxs) ] Σ[ k ∈ Fin (length (xxs ! j)) ] (concat xxs) ! i ≡ (xxs ! j) ! k
concat-index (xs ∷ xxs) (fin i ⦃ q ⦄)  with holds? (i <n length xs)
... | yes p = fzero , fin i ⦃ p ⦄ , {! !}
... | no ¬p = (fsuc $ rec .fst) , rec .snd .fst , {! rec .snd .snd !} where
  q₁ : length xs ≤n i
  q₁ = ≤-from-not-< _ _ ¬p

  q₂ : suc i - length xs ≡ suc (i - length xs)
  q₂ = monus-≤-suc _ _ q₁

  q₃ : i <n length xs + length (concat xxs)
  q₃ = subst (λ a → i <n a) (length-++ {xs = xs}) q

  q₄ : suc i - length xs ≤n length (concat xxs)
  q₄ = {! !}

  q₅ : (i - length xs) <n length (concat xxs)
  q₅ = subst (λ a → a ≤n length (concat xxs)) q₂ q₄
  rec = concat-index xxs $ fin (i - length xs) ⦃ q₅ ⦄

concat-index-sum
  : ∀ {A : Type ℓa} {xxs : List $ List A} i
  → (concat-index xxs i) .fst .lower + (concat-index xxs i) .snd .fst .lower ≡ᵢ i .lower
concat-index-sum = ?

concat-index-lt
  : ∀ {A : Type ℓa} {xxs : List $ List A} i j → i ≤ j
  → (concat-index xxs i) .fst ≤ (concat-index xxs j) .fst
concat-index-lt = ?

concat-sorted
  : {xxs : List $ List A}
  → (∀ i → is-sorted R (xxs ! i))
  → is-sorted (λ l m → ∀ i j → R (l ! i) (m ! j)) xxs
  → is-sorted R (concat xxs)
concat-sorted = ?
```
