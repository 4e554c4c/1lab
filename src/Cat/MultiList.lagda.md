<!--
```agda
--open import 1Lab.Reflection.HLevel
--open import 1Lab.HLevel.Closure
--open import 1Lab.Type hiding (id ; _∘_)
--open import Data.Fin.Product
--open import Data.Fin.Base
--open import 1Lab.Reflection
--open import Data.Vec.Base
--
open import 1Lab.Underlying
open import 1Lab.HLevel
open import 1Lab.Path

open import Cat.Prelude

open import Data.List.Properties
open import Data.Product.NAry
open import Data.List.Base
```
-->

```agda
module Cat.MultiList (o ℓ : Level) where
```

# Multicategories {defines=multicategory}

<!--
```agda
```
-->

```agda

level-of-multi : Level
level-of-multi = lsuc (o ⊔ ℓ)

record MultiData : Type level-of-multi where
  no-eta-equality
  field
    Ob : Type o

    MHom : List Ob → Ob → Type ℓ
    MHom-set : ∀ {xs y} → is-set (MHom xs y)
    Mid  : ∀ {x}     → MHom [ x ] x

  MultiHom = List $ Σ[ ys ∈ List Ob ] Σ[ z ∈ Ob ] MHom ys z

  --_M++_ : ∀ {xs ys xs' ys'} → MultiHom xs ys → MultiHom xs' ys' → MultiHom (xs ++ xs') (ys ++ ys')
  --M[] M++ ms' = ms'
  --_M++_ {xs} {ys} {xs'} {ys'} (Mcons {xs''} {y} {xs'''} {ys''} h ms) ms' =
  --  transport (λ i → MultiHom (++-assoc xs'' xs''' xs' (~ i)) (y ∷ (ys'' ++ ys'))) $ Mcons h (ms M++ ms')

  bottom : MultiHom → List Ob
  bottom [] = []
  bottom ((_ , z , _) ∷ xs) = z ∷ bottom xs

  top : MultiHom → List Ob
  top [] = []
  top ((ys , _ , _) ∷ xs) = ys ++ bottom xs

  idM  : (xs : List Ob) → MultiHom
  idM [] = []
  idM (x ∷ xs) = ([ x ] , x , (Mid {x})) ∷ idM xs


  lemma : ∀ xs → bottom (idM xs) ≡ xs
  lemma [] = refl
  lemma (x ∷ xs) i = x ∷ lemma xs i

  single : ∀ {xs z} → MHom xs z → MultiHom
  single {xs} {z} f = (xs , z , f) ∷ []


record MultiStructure (d : MultiData) : Type level-of-multi  where
  no-eta-equality
  open MultiData d public

  field
    _⨟_ : ∀ {z}
          → (h : MultiHom)
          → MHom (bottom h) z
          → MHom (top h) z

{-
  _M⨟_ : ∀ {xs ys zs}
       → MultiHom xs ys
       → MultiHom ys zs
       → MultiHom xs zs
  _M⨟_ {[]} {ys} {[]} M[] M[] = M[]
  _M⨟_ {xs} {ys} {zs} m1 (Mcons {xs'} {y} {xs''} {ys'} m m2) = transport (λ i → MultiHom (split.p i) (y ∷ ys')) $ Mcons (split.h₁ ⨟ m) (split.h₂ M⨟ m2)
    where module split = Msplit (msplit {xs} {xs'} {xs''} m1)
-}

record MultiLaws {d} (s : MultiStructure d) : Type level-of-multi where
  open MultiStructure s public

  field
    idr : ∀ {xs z}
        → (f : MHom xs z)
        → idM xs ⨟ f ≡ f
{-

    idl : ∀ {xs z}
        → (f : MHom xs z)
        → single f ⨟ Mid ≡ f

    assoc : ∀ {ws xs ys z}
        → (f : MultiHom ws xs)
        → (g : MultiHom xs ys)
        → (h : MHom ys z)
        → f ⨟ (g ⨟ h) ≡ ((f M⨟ g) ⨟ h)


record MultiCategory : Type level-of-multi where
  field
    base : MultiData
    structure : MultiStructure base
    laws : MultiLaws structure

-}
