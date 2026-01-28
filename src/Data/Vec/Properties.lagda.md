<!--
```agda
open import 1Lab.Prelude

open import Data.Nat.Properties
open import Data.Product.NAry
open import Data.List.Base hiding (head ; tail ; lookup) renaming (tabulate to tabulateℓ ; _++_ to _++ℓ_ ;_!_ to _!ℓ_; [] to []ℓ)
open import Data.Fin.Base
open import Data.Fin.Closure using (sum)

import Data.Vec.Base as Vec

open Vec
```
-->

```agda
module Data.Vec.Properties where
```

<!--
```agda
private variable
  ℓ : Level
  A B C : Type ℓ
  n k l m : Nat
  xs ys zs : Vec A n
```
-->

# Properties of vectors

```agda
tabulate-lookup : (xs : Vec A n) → tabulate (lookup xs) ≡ xs
tabulate-lookup v with vec-view v
... | []       = refl
... | (x ∷ xs) = ap (x ∷v_) (tabulate-lookup xs)

lookup-tabulate : (xs : Fin n → A) (i : Fin n) → lookup (tabulate xs) i ≡ xs i
lookup-tabulate xs i with fin-view i
... | zero  = refl
... | suc i = lookup-tabulate (xs ∘ fsuc) i

lookup-is-equiv : is-equiv (lookup {A = A} {n})
lookup-is-equiv = is-iso→is-equiv $
  iso tabulate (λ x → funext (lookup-tabulate x)) tabulate-lookup

module Lookup {ℓ} {A : Type ℓ} {n : Nat} = Equiv (lookup {A = A} {n} , lookup-is-equiv)

map-lookup : {A B : Type ℓ} (f : A → B) (xs : Vec A n) → ∀ i → lookup (map f xs) i ≡ f (lookup xs i)
map-lookup f v i with vec-view v | fin-view i
... | (x ∷ xs) | zero  = refl
... | (x ∷ xs) | suc i = map-lookup f xs i

lookup-! : ∀ {xs : List A} (n : Fin (length xs)) → lookup (vec xs) n ≡ xs !ℓ n
lookup-! n = refl

map-id : {A : Type ℓ} (xs : Vec A n) → map (λ x → x) xs ≡ xs
map-id xs = Lookup.injective₂ (funext λ i → map-lookup _ xs i) refl

--flatten : {ms : Fin n → Nat} → (∀ j → Vec A (ms j)) → Vec A (sum n ms)
--flatten {n = zero} vs = vec (concat {! !})

map-comp
  : {A : Type ℓ} (xs : Vec A n) (f : A → B) (g : B → C)
  → map (λ x → g (f x)) xs ≡ map g (map f xs)
map-comp xs f g = Lookup.injective $ funext λ i →
  lookup (map (λ x → g (f x)) xs) i ≡⟨ map-lookup (λ x → g (f x)) xs i ⟩
  g (f (lookup xs i))               ≡˘⟨ ap g (map-lookup f xs i) ⟩
  g (lookup (map f xs) i)           ≡˘⟨ map-lookup g (map f xs) i ⟩
  lookup (map g (map f xs)) i       ∎
```
