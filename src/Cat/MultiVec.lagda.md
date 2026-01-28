<!--
```agda
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Closure
open import 1Lab.Underlying
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type hiding (id ; _∘_)

open import Cat.Base

open import Data.Nat.Properties
open import Data.Vec.Properties
open import Data.Product.NAry
open import Data.Fin.Closure
open import Data.Fin.Product
open import Data.Fin.Base
open import Data.Vec.Base
```
-->

```agda
module Cat.MultiVec {o ℓ : Level} where

```

# Multicategories {defines=multicategory}

<!--
```agda
```
-->

```agda

postulate

  sum-1 : ∀ n → sum n (λ k → 1) ≡ n

record Operad : Type (lsuc ℓ) where
  no-eta-equality
  field
    -- ⊤ = Ob : Type o
    Arr : Nat → Type ℓ
    -- Arr : tt x tt ... <n> ... x tt -> tt
    id : Arr 1

    _∘[_]_
      : ∀ {n m}
      → Arr (suc n)
      → (k : Fin (suc n))
      → Arr m
      → Arr (n + m)


  -- such that, identity:
    idr-∘[_]
      : ∀ {n} (k : Fin (suc n)) → (a : Arr (suc n))
      → PathP (λ i → Arr (+-oner n i))
        (a ∘[ k ] id)
        a

    idl-∘
      : ∀ m → (a : Arr m)
      → id ∘[ fzero ] a ≡ a

record Operad' : Type (lsuc ℓ) where
  no-eta-equality
  field
    -- ⊤ = Ob : Type o
    Arr : Nat → Type ℓ
    -- Arr : tt x tt ... <n> ... x tt -> tt
    id : Arr 1

    _⊙[_]_
      : ∀ {n}
      → Arr n
      → (m : Fin n → Nat)
      → (∀ k → (Arr $ m k))
      → Arr (sum n m) -- ∑_n (m n)


    idr-⊙
      : ∀ {n} (a : Arr n)
      → PathP (λ i → Arr (sum-1 n i))
        (a ⊙[ (λ k → 1) ] (λ k → id))
        a

    idl-⊙
      : ∀ {n} (a : Arr n)
      → PathP (λ i → Arr (+-zeror n i))
        (id ⊙[ (λ _ → n) ] λ _ → a)
        a

Πᶠ' : ∀ {n ℓ} (P : (i : Fin n) → Type ℓ) → Type ℓ
Πᶠ' {n = 0} P     = Lift _ ⊤
Πᶠ' {n = suc n} P = P fzero × Πᶠ' λ i → P (fsuc i)

record MultiCatVec : Type (lsuc o ⊔ lsuc ℓ) where
  no-eta-equality
  field
    Ob : Type o
    Hom : ∀ {n} → (xs : Vec Ob n) → (y : Ob) → Type ℓ
    _∘_ : ∀ {n m} → {x : Vec (Vec Ob m) n} {y : Vec Ob n} → ∀ {z}
         → Hom y z → Πᶠ' (λ i → Hom (lookup x i) (lookup y i)) → Hom (concatV x) z

{-
    id : ∀ {x : Ob} → Hom [ x ] x
    _∘_
      : ∀ {n m} → {x : Vec Ob n} {y : Vec Ob m} → ∀ {z} {k : Fin m}
      → Hom x (lookup y k)
      → Hom y z
--      → Hom {! insert !} z
-}

  data MultiHom : {n m : Nat} → Vec Ob n → Vec Ob m → Type (o ⊔ ℓ) where
    M[] : MultiHom [] []
    Mcons : ∀ {n m xs y xs' ys'} → Hom {n} xs y → MultiHom {n} {m} xs' ys' → MultiHom (xs ++ xs') (y ∷ ys')

  _M++_ : ∀ {n m n' m' xs ys xs' ys'} → MultiHom {n} {m} xs ys → MultiHom {n'} {m'} xs' ys' → MultiHom (xs ++ xs') (ys ++ ys')
  M[] M++ ms' = ms'
  _M++_ {xs = xs} {ys} {xs'} {ys'} (Mcons {xs = xs''} {y} {xs'''} {ys''} h ms) ms' =
    transport (λ i → MultiHom (++-assoc xs'' xs''' xs' i) (y ∷ (ys'' ++ ys'))) $ Mcons {!h !} {! !} --Mcons h {! (ms M++ ms') !}

```
