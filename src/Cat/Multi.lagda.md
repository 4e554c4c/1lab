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
module Cat.Multi (o ℓ : Level) where
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

  data MultiHom : List Ob → List Ob → Type (o ⊔ ℓ) where
    M[] : MultiHom [] []
    Mcons : ∀ {xs y xs' ys'} → MHom xs y → MultiHom xs' ys' → MultiHom (xs ++ xs') (y ∷ ys')

  _M++_ : ∀ {xs ys xs' ys'} → MultiHom xs ys → MultiHom xs' ys' → MultiHom (xs ++ xs') (ys ++ ys')
  M[] M++ ms' = ms'
  _M++_ {xs} {ys} {xs'} {ys'} (Mcons {xs''} {y} {xs'''} {ys''} h ms) ms' =
    transport (λ i → MultiHom (++-assoc xs'' xs''' xs' (~ i)) (y ∷ (ys'' ++ ys'))) $ Mcons h (ms M++ ms')

  record Msplit {l} (r₁ r₂ : List Ob) (h : MultiHom l (r₁ ++ r₂)) : Type (lsuc o ⊔ lsuc ℓ) where
    field
      {l₁} : List Ob
      {l₂} : List Ob
      p   : l₁ ++ l₂ ≡ l
      h₁  : MultiHom l₁ r₁
      h₂  : MultiHom l₂ r₂

  -- we can split on the bottom of a multihom but recovering the top split definitionally is impossible.
  -- instead we provide a proof that the top splits well
  msplit : ∀ {l r₁ r₂ : List Ob}
          → (h : MultiHom l (r₁ ++ r₂))
          → Msplit r₁ r₂ h
  msplit {l} {[]} {r₂} h = record { p = refl ; h₁ = M[] ; h₂ = h }
  msplit {l} {x ∷ r₁} {r₂} (Mcons {xs = xs} {xs' = xs'} m ml) = record
    { l₁ = xs ++ split.l₁
    ; l₂ = split.l₂
    ; p = ++-assoc xs split.l₁ split.l₂ ∙ ap (xs ++_) split.p
    ; h₁ = Mcons m split.h₁
    ; h₂ = split.h₂
    } where
    split = msplit {xs'} {r₁} {r₂} ml
    module split = Msplit split

  idM  : ∀ {xs} → MultiHom xs xs
  idM {[]} = M[]
  idM {x ∷ xs} = Mcons (Mid {x}) idM

  single : ∀ {xs z} → MHom xs z → MultiHom xs [ z ]
  single {xs} {z} f = transport (λ i → MultiHom (++-idr xs i) [ z ]) $ Mcons f M[]

record MultiStructure (d : MultiData) : Type level-of-multi  where
  no-eta-equality
  open MultiData d public

  field
    _⨟_ : ∀ {xs ys z}
          → MultiHom xs ys
          → MHom ys z
          → MHom xs z

  _M⨟_ : ∀ {xs ys zs}
       → MultiHom xs ys
       → MultiHom ys zs
       → MultiHom xs zs
  _M⨟_ {[]} {ys} {[]} M[] M[] = M[]
  _M⨟_ {xs} {ys} {zs} m1 (Mcons {xs'} {y} {xs''} {ys'} m m2) = transport (λ i → MultiHom (split.p i) (y ∷ ys')) $ Mcons (split.h₁ ⨟ m) (split.h₂ M⨟ m2)
    where module split = Msplit (msplit {xs} {xs'} {xs''} m1)

record MultiLaws {d} (s : MultiStructure d) : Type level-of-multi where
  open MultiStructure s public

  field
    idr : ∀ {xs z}
        → (f : MHom xs z)
        → idM ⨟ f ≡ f

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

{-
record MultiCat' : Type level-of-multi where
  no-eta-equality
  field
    Ob : Type o

    Hom : List Ob → Ob → Type ℓ
    Hom-set : ∀ {xs y} → is-set (Hom xs y)
    id  : ∀ {x}     → Hom [ x ] x

    _∘_ : ∀ {xs ys y ys' z}
          → Hom xs y
          → Hom (ys ++ [ y ] ++ ys') z
          → Hom (ys ++ xs ++ ys') z
record MultiData : Type level-of-multi where
  no-eta-equality
  field
    Ob : Type o

    Hom : List Ob → Ob → Type ℓ
    Hom-set : ∀ {xs y} → is-set (Hom xs y)
    id  : ∀ {x}     → Hom [ x ] x

  data MultiHom : List Ob → List Ob → Type (o ⊔ ℓ) where
    M[] : MultiHom [] []
    Mcons : ∀ {xs y xs' ys'} → Hom xs y → MultiHom xs' ys' → MultiHom (xs ++ xs') (y ∷ ys')

  _M++_ : ∀ {xs ys xs' ys'} → MultiHom xs ys → MultiHom xs' ys' → MultiHom (xs ++ xs') (ys ++ ys')
  M[] M++ ms' = ms'
  _M++_ {xs} {ys} {xs'} {ys'} (Mcons {xs''} {y} {xs'''} {ys''} h ms) ms' =
    transport (λ i → MultiHom (++-assoc xs'' xs''' xs' (~ i)) (y ∷ (ys'' ++ ys'))) $ Mcons h (ms M++ ms')

  record Msplit {l} (r₁ r₂ : List Ob) (h : MultiHom l (r₁ ++ r₂)) : Type (lsuc o ⊔ lsuc ℓ) where
    field
      {l₁} : List Ob
      {l₂} : List Ob
      p   : l₁ ++ l₂ ≡ l
      h₁  : MultiHom l₁ r₁
      h₂  : MultiHom l₂ r₂

  -- we can split on the bottom of a multihom but recovering the top split definitionally is impossible.
  -- instead we provide a proof that the top splits well
  msplit : ∀ {l r₁ r₂ : List Ob}
          → (h : MultiHom l (r₁ ++ r₂))
          → Msplit r₁ r₂ h
  msplit {l} {[]} {r₂} h = record { p = refl ; h₁ = M[] ; h₂ = h }
  msplit {l} {x ∷ r₁} {r₂} (Mcons {xs = xs} {xs' = xs'} m ml) = record
    { l₁ = xs ++ split.l₁
    ; l₂ = split.l₂
    ; p = ++-assoc xs split.l₁ split.l₂ ∙ ap (xs ++_) split.p
    ; h₁ = Mcons m split.h₁
    ; h₂ = split.h₂
    } where
    split = msplit {xs'} {r₁} {r₂} ml
    module split = Msplit split

  idM  : ∀ {xs} → MultiHom xs xs
  idM {[]} = M[]
  idM {x ∷ xs} = Mcons (id {x}) idM

  single : ∀ {xs z } → Hom xs z → MultiHom xs [ z ]
  single {xs} {z} f = transport (λ i → MultiHom (++-idr xs i) [ z ]) $ Mcons f M[]

record MultiStructure (d : MultiData) : Type level-of-multi  where
  no-eta-equality
  open MultiData d public

  field
    _∘_ : ∀ {xs ys z}
          → MultiHom xs ys
          → Hom ys z
          → Hom xs z

  _M∘_ : ∀ {xs ys zs}
       → MultiHom xs ys
       → MultiHom ys zs
       → MultiHom xs zs
  _M∘_ {[]} {ys} {[]} M[] M[] = M[]
  {-# CATCHALL #-}
  _M∘_ {xs} {ys} {zs} m1 (Mcons {xs'} {y} {xs''} {ys'} m m2) = transport (λ i → MultiHom (split.p i) (y ∷ ys')) $ Mcons (split.h₁ ∘ m) (split.h₂ M∘ m2)
    where module split = Msplit (msplit {xs} {xs'} {xs''} m1)

record MultiLaws {d} (s : MultiStructure d) : Type level-of-multi where
  open MultiStructure s public

  field
    idr : ∀ {xs z}
        → (f : Hom xs z)
        → idM ∘ f ≡ f

    idl : ∀ {xs z}
        → (f : Hom xs z)
        → single f ∘ id ≡ f

    assoc : ∀ {ws xs ys z}
        → (𝔣 : MultiHom ws xs)
        → (𝔤 : MultiHom xs ys)
        → (h : Hom ys z)
        → 𝔣 ∘ (𝔤 ∘ h) ≡ ((𝔣 M∘ 𝔤) ∘ h)
-}
