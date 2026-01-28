<!--
```agda
--open import 1Lab.Reflection.HLevel
--open import 1Lab.HLevel.Closure
--open import 1Lab.Type hiding (id ; _∘_)
--open import 1Lab.Reflection
--open import Data.Vec.Base
--
--open import Data.List.Properties
--open import Data.List.Base
open import 1Lab.Underlying
open import 1Lab.HLevel
open import 1Lab.Path

open import Cat.Prelude

open import Data.Fin.Properties
open import Data.Product.NAry
open import Data.Fin.Product
open import Data.Fin.Base
```
-->

```agda
module Cat.MultiFin (o ℓ : Level) where
```

# Multicategories {defines=multicategory}

<!--
```agda
```
-->

```agda

VecF : ∀ {ℓ} (A : Type ℓ) → Nat → Type ℓ
VecF A n = Fin n → A

instance
  From-prod-Vec : ∀ {ℓ} {A : Type ℓ} → From-product A (VecF A)
  From-prod-Vec {A = A} .From-product.from-prod = go where
    go : ∀ n → Vecₓ A n → VecF A n
    go zero xs                ()
    go (suc zero) x _ = x
    go (suc n@(suc _)) (x , xs) k with fin-view k
    ... | zero = x
    ... | suc l = go n xs l

--s : VecF Nat 3
--s = [ 1 , 2 , 7 ]
--
--n : Nat
--n = s 2

level-of-multi : Level
level-of-multi = lsuc (o ⊔ ℓ)

record MultiData : Type level-of-multi where
  no-eta-equality
  field
    Ob : Type o

    MHom : ∀ {n} → (Fin n → Ob) → Ob → Type ℓ
    MHom-set : ∀ {n} {xs : VecF Ob n} {y} → is-set (MHom xs y)
    Mid  : ∀ {x}     → MHom [ x ] x

  field
    _∘[_]_ : ∀ {n m z}
          {ys : VecF Ob n}
          → MHom ys z
          → (k : Fin n)
          {xs : VecF Ob m}
          → MHom xs (ys k)
          → MHom {n = n + m} (ys [ k ← xs ]) z

record MultiLaws (d : MultiData) : Type level-of-multi where
  open MultiData d public

  field
    idr[_] : ∀ {n z} {xs : VecF Ob n} k
        → (f : MHom xs z)
        → PathP (λ i → MHom (insertvec-insert xs k i) z)
          {! (f ∘[ k ] Mid) !}
          f
{-

    idl : ∀ {xs z}
        → (f : MHom xs z)
        → single f ⨟ Mid ≡ f

    assoc : ∀ {ws xs ys z}
        → (f : MultiHom ws xs)
        → (g : MultiHom xs ys)
        → (h : MHom ys z)
        → f ⨟ (g ⨟ h) ≡ ((f M⨟ g) ⨟ h)

-}
