<!--
```agda
open import 1Lab.Underlying
open import 1Lab.HLevel
open import 1Lab.Path

open import Cat.Functor.Bifunctor
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Univalent
open import Cat.Prelude
open import Cat.Multi

open import Data.List.Properties
open import Data.Product.NAry
open import Data.List.Base

import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Multi.Instances.Monoidal
  {o ℓ} {C : Precategory o ℓ}
  (Cᵐ : Monoidal-category C) where
private
  open module C = Cr C
open Monoidal-category Cᵐ
--private
```

# The multicategory category for a monoidal category


```agda
⨂ : List Ob → Ob
⨂ [] = Unit
⨂ (x ∷ l) = x ⊗ ⨂ l

module monoidal→multi where
--: MultiCategory o ℓ
--monoidal→multi = record where
  base : MultiData o ℓ
  base = record where
    Ob = C.Ob
    MHom x y = Hom (⨂ x) y
    MHom-set = hlevel 2
    Mid {x} = ρ←
  open MultiData base


  lem₁ : ∀ {xs ys} → ⨂ (xs ++ ys) ≅ ⨂ xs ⊗ ⨂ ys
  lem₁ {[]} {ys} = λ≅
  lem₁ {x ∷ xs} {ys} = α≅ Iso⁻¹ ∘Iso (F-map-iso (Right -⊗- x) $ lem₁ {xs} {ys})
  module lem₁ {xs} {ys} = _≅_ (lem₁ {xs} {ys})

  lem₁' : ∀ xs → PathP (λ i → (⨂ (++-idr xs i)) ≅ (⨂ xs ⊗ Unit)) (lem₁ {xs} {[]}) ρ≅
  lem₁' [] = ≅-path-from (Monoidal.λ≡ρ Cᵐ)
  lem₁' xs@(x ∷ xs') = ≅-pathp-from {a = ⨂ (xs ++ [])} {c = ⨂ xs} (λ i → ⨂ (++-idr xs i)) (λ i → ⨂ xs ⊗ Unit) need
    where
    rec : PathP (λ i → ⨂ (++-idr xs' i) ≅ (⨂ xs' ⊗ Unit)) (lem₁ {xs'}) ρ≅
    rec = lem₁' xs'
    need : PathP (λ i → Hom ((⨂ xs) ⊗ Unit) (⨂ (++-idr xs i))) ((x ▶ lem₁.from {xs'}) ∘ α→ x (⨂ xs') Unit) ρ←
    need = Hom-pathp-reflr C $
      (path→iso (λ i → x ⊗ ⨂ (++-idr xs' i))) ._≅_.to  ∘ (x ▶ lem₁.from {xs'}) ∘ α→ x (⨂ xs') Unit
        ≡⟨ pulll (from-pathp-to C _ (apd (λ i a → x ▶ a ._≅_.from) rec)) ⟩
      (x ▶ ρ←) ∘ α→ x (⨂ xs') Unit
        ≡⟨ Monoidal.triangle-ρ← Cᵐ ⟩
      ρ← ∎
  -- first some lemmas
  -- since our multicategory is representable, we have a representing object for each list
  MultiHom→hom : ∀ {xs ys} → MultiHom xs ys → Hom (⨂ xs) (⨂ ys)
  MultiHom→hom M[] = C.id
  MultiHom→hom (Mcons {xs = xs} {xs' = xs'} x m) = (x ⊗₁ MultiHom→hom m) ∘ lem₁.to {xs} {xs'}

  structure : MultiStructure o ℓ base
  structure = record { _⨟_ = λ m h → h ∘ MultiHom→hom m }

  lem₂ : ∀ xs → MultiHom→hom (idM {xs}) ≡ id {⨂ xs}
  lem₂ [] = refl
  lem₂ (x ∷ xs) =
    (ρ← ⊗₁ MultiHom→hom (idM {xs})) ∘ α← x Unit (⨂ xs) ∘ (x ▶ λ→) ≡⟨ ⊗.⟨ Σ-pathp refl (lem₂ xs) ⟩ ⟩∘⟨refl ⟩
    (ρ← ⊗₁ (id {⨂ xs})) ∘ α← x Unit (⨂ xs) ∘ (x ▶ λ→)             ≡⟨⟩
    (ρ← ◀ ⨂ xs) ∘ α← x Unit (⨂ xs) ∘ (x ▶ λ→)                     ≡⟨ pulll triangle ⟩
    (x ▶ λ←) ∘ (x ▶ λ→)                                           ≡˘⟨ ▶.F-∘ _ _ ⟩
    x ▶ (λ← ∘ λ→)                                                 ≡⟨ ▶.elim (λ≅ .invr) ⟩
    id                                                            ∎

  lem₃ : ∀ {xs z} → (f : Hom (⨂ xs) z) → MultiHom→hom {xs} {[ z ]} (single f) ≡ ρ→ ∘ f
  lem₃ {xs} {z} f = lem₃' ∙ (sym $ unitor-r .Cr.to ._=>_.is-natural _ _ _) where
    lem₃' : MultiHom→hom {xs} {[ z ]} (single f) ≡ (f ◀ Unit) ∘ ρ→
    lem₃' i = comp (λ j → Hom (⨂ (++-idr xs j)) (⨂ [ z ])) (∂ i) λ where
      j (i = i0) → MultiHom→hom {++-idr xs j} {[ z ]} (transp (λ i → MultiHom (++-idr xs (i ∧ j)) [ z ]) (~ j) (Mcons f M[]))
      j (j = i0) → MultiHom→hom {xs ++ []} {[ z ]} $ Mcons f M[]
      j (i = i1) → (f ⊗₁ id) ∘ lem₁' xs j ._≅_.to

  open MultiStructure structure using (_⨟_; _M⨟_ )


  Multi-Hom-distr : ∀ {xs ys zs} (f : MultiHom xs ys) (g : MultiHom ys zs) →
     MultiHom→hom (f M⨟ g ) ≡ MultiHom→hom g ∘ MultiHom→hom f
  Multi-Hom-distr {[]} {ys} {[]} M[] M[] = sym $ idl _
  Multi-Hom-distr {xs} {ys} {zs} m1 (Mcons {xs'} {y} {xs''} {ys'} m m2) =
    -- can't substitute for definition :(
    --MultiHom→hom {xs} (transport (λ i → MultiHom (split.p i) (y ∷ ys')) $ Mcons (split.h₁ ⨟ m) (split.h₂ M⨟ m2))
    MultiHom→hom {xs} (m1 M⨟ Mcons m m2)
      ≡⟨ ? ⟩
    MultiHom→hom (Mcons m m2) ∘ MultiHom→hom m1 ∎
    --transport (λ i → MultiHom (split.p i) (y ∷ ys')) $ Mcons (split.h₁ ∘ m) (split.h₂ M∘ m2)
    where module split = Msplit (msplit {xs} {xs'} {xs''} m1)

  laws : MultiLaws o ℓ structure
  laws .MultiLaws.idr {xs} f = (refl⟩∘⟨ lem₂ xs) ∙ C.idr f
  laws .MultiLaws.idl {xs} f =
    ρ← ∘ MultiHom→hom {xs} (single f) ≡⟨ refl⟩∘⟨ lem₃ {xs} f ⟩
    ρ← ∘ ρ→ ∘ f                       ≡⟨ cancell (ρ≅ .invr) ⟩
    f                                 ∎
  laws .MultiLaws.assoc {ws} {xs} {ys} {z} f g h =
    (h ∘ MultiHom→hom g) ∘ MultiHom→hom f ≡⟨ {! !} ⟩
    h ∘ MultiHom→hom (f M⨟ g )            ∎


monoidal→multi : MultiCategory o ℓ
monoidal→multi = record { monoidal→multi }

```
