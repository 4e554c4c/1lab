<!--
```agda
open import 1Lab.Path
open import 1Lab.Type

open import Data.Product.NAry
open import Data.List.Base --(renaming [] to []ℓ
open import Data.Fin.Base
open import Data.Nat.Base
open import Data.Id.Base
open import Data.Irr

open import Meta.Idiom
```
-->

```agda
module Data.Vec.Refinement where
```

# Vectors


```agda

private variable
  ℓ : Level
  A B C : Type ℓ
  n k : Nat

data Length {ℓ} {A : Type ℓ} : List A → Nat → Type ℓ where
  zero : Length [] zero
  suc  : ∀ {x xs n} → Length xs n → Length (x ∷ xs) (suc n)

instance
  Length-zero : Length {A = A} [] zero
  Length-zero = zero

  Length-suc : ∀ {x n} {xs : List A} → ⦃ _ : Length xs n ⦄
    → Length (x ∷ xs) (suc n)
  Length-suc ⦃ l ⦄ = suc l

  Length-length : ∀ {xs : List A} → Length xs (length xs)
  Length-length {xs = []} = zero
  Length-length {xs = x ∷ xs} = suc Length-length


length-uncons : ∀ {xs n x} → Length {A = A} (x ∷ xs) (suc n) → Length xs n
length-uncons (suc l) = l

record Vec {ℓ} (A : Type ℓ) (n : Nat) : Type ℓ where
  constructor vec
  field
    lower   : List A
    ⦃ len ⦄ : Irr (Length lower n)

--open Vec

pattern []v = vec []

infixr 20 _∷v_
_∷v_ : ∀ {n} → A → Vec A n → Vec A (suc n)
_∷v_ v (vec vs ⦃ p ⦄) = vec (v ∷ vs) ⦃ suc <$> p ⦄

--pattern _∷v_ y ys = vec (y ∷ (Vec.lower ys))

data Vec-view {ℓ} {A : Type ℓ} : {n : Nat} → Vec A n → Type ℓ where
  []     : Vec-view {n = 0} []v
  _∷_  : ∀ {n} (a : A) → (vs : Vec A n) → Vec-view {n = suc n} (a ∷v vs)

vec-view : ∀ {n} (v : Vec A n) → Vec-view v
vec-view {n = zero} (vec []) = []
vec-view {n = suc k} (vec (x ∷ l) ⦃ p ⦄) = x ∷ vec l ⦃ length-uncons <$> p ⦄

list→vec : (xs : List A) → Vec A (length xs)
list→vec xs = vec xs

headv : Vec A (suc n) → A
headv (vec (x ∷ xs)) = x

tailv : Vec A (suc n) → Vec A n
tailv v with vec-view v
... | x ∷ xs = xs

lookupv : Vec A n → Fin n → A
lookupv xs n with fin-view n
... | zero  = headv xs
... | suc i = lookupv (tailv xs) i

tabulatev : ∀ {n} (f : Fin n → A) → Vec A n
tabulatev {n = zero}  f = []v
tabulatev {n = suc n} f = f fzero ∷v tabulatev (f ∘ fsuc)

instance
  From-prod-Vec : From-product A (Vec A)
  From-prod-Vec .From-product.from-prod = go where
    go : ∀ n → Vecₓ A n → Vec A n
    go zero xs                = []v
    go (suc zero) xs          = xs ∷v []v
    go (suc (suc n)) (x , xs) = x ∷v go (suc n) xs

_++v_ : ∀ {n k} → Vec A n → Vec A k → Vec A (n + k)
xs ++v ys with vec-view xs
...| [] = ys
...| (x ∷ xs) = x ∷v (xs ++v ys)

concatV : ∀ {n m} → Vec (Vec A m) n → Vec A (n * m)
concatV v with vec-view v
... | [] = []v
... | a ∷ as = a ++v concatV as

_ : Path (Vec Nat 3) [ 1 , 2 , 3 ] (1 ∷v 2 ∷v 3 ∷v []v)
_ = refl
```
