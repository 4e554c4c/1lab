<!--
```agda
open import 1Lab.Underlying
open import 1Lab.HLevel
open import 1Lab.Path

open import Cat.Instances.FinSets.Kleisli
open import Cat.Displayed.BeckChevalley
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Functor
open import Cat.Functor.Bifunctor
open import Cat.Displayed.Operad
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Univalent
open import Cat.Prelude
open import Cat.Multi

open import Data.List.Properties
open import Data.Product.NAry
open import Data.Finset.Base
open import Data.List.Base hiding (lookup)
open import Data.Dec.Base
open import Data.Vec.Base
open import Data.Maybe
open import Data.Fin

import Cat.Displayed.IsoFibration
import Cat.Displayed.Cocartesian
import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Multi.Instances.DisplayedMonoidal
  {o ℓ} {C : Precategory o ℓ}
  (Cᵐ : Monoidal-category C) where
private
  open module C = Cr C
open Monoidal-category Cᵐ
--private
```

# The operad for a monoidal category


```agda

⨂ : ∀{n} → (Fin n → Ob) → Ob
⨂ {zero} v = Unit
⨂ {1} v = v 0
⨂ {suc n@(suc _)} v = (v 0) ⊗ ⨂ λ x → v (fsuc x)

⨂₁ : ∀{n} → {vs vd : Fin n → Ob} → (h : (k : Fin n) → Hom (vs k) (vd k)) → Hom (⨂ vs) (⨂ vd)
⨂₁ {zero} _ = id
⨂₁ {1} f = f 0
⨂₁ {suc n@(suc _)} h = h 0 ⊗₁ ⨂₁ λ k → h (fsuc k)

module _ {n m} (f : Fin n → Maybe (Fin m)) (v : Fin n → Ob) where
  where-defined : Fin n → Ob
  where-defined k = Maybe-rec (λ _ → v k) Unit (f k)
  --fibre-listing : Listing (fibre f (just k))
  --fibre-listing = Listing-Σ

-- a vector is "less defined" than another if it contains more units
data _≼_ : ∀ {n} → (Vec Ob n) → (Vec Ob n) → Type o where
  refd : ∀ {n} (v : Vec Ob n) → v ≼ v
  unitd : ∀ {n} (v⁻ v : Vec Ob n) x → (v⁻ ≼ v) → (Unit ∷ v⁻) ≼ (x ∷ v)

⨂-vec : ∀{n} → (Vec Ob n) → Ob
⨂-vec [] = Unit
⨂-vec (a ∷ []) = a
⨂-vec (a ∷ as@(_ ∷ _)) = a ⊗ ⨂-vec as

⨂₁-vec : ∀ {n} → {vs vd : Vec Ob n} → (h : (k : Fin n) → Hom (lookup vs k) (lookup vd k)) → Hom (⨂-vec vs) (⨂-vec vd)
⨂₁-vec {vs = []} {vd = []} _ = id
⨂₁-vec {vs = a ∷ []} {vd = x ∷ []} h = h 0
⨂₁-vec {vs = a ∷ as@(_ ∷ _)} {vd = x ∷ bs@(_ ∷ _)} h = h 0 ⊗₁ ⨂₁-vec λ k → h (fsuc k)

≼→Hom : ∀ {n} → {v⁻ v : Vec Ob n} → (v⁻ ≼ v) → Hom (⨂-vec v) (⨂-vec v⁻)
≼→Hom {vs} {vd} (refd v) = id
≼→Hom {vs} {vd} (unitd v- v x p) = {! ≼→Hom p  !}

maybe-vec : ∀ {n} (f : Fin n → Maybe Ob) → (Fin n → Ob)
maybe-vec f k with f k
... | just o  = o
... | nothing = Unit

module _ {n m} (f : Fin n → Maybe (Fin m)) (k : Fin m) where
  --fibre-listing : Listing (fibre f (just k))
  --fibre-listing = Listing-Σ

  --fibre-card : Nat
  --fibre-card = length $ Listing.univ fibre-listing

  --fibre-vec : (Fin fibre-card) → Fin n
  --fibre-vec l = (Listing.univ fibre-listing ! l) .fst
  fibre-subvec : (Fin n → Ob) → (Fin n → Ob)
  fibre-subvec v l = ifᵈ f l ≡ᵢ? (just k) then v l else Unit

  --⨂₁  but for subvecs
  subvec₁ : {vs vd : Fin n → Ob} → (h : (k : Fin n) → Hom (vs k) (vd k)) → Hom (⨂ $ fibre-subvec vs) (⨂ $ fibre-subvec vd)
  subvec₁ {vs} {vd} h = ⨂₁ helper
    where
    helper : (l : Fin n) → Hom (fibre-subvec vs l) (fibre-subvec vd l)
    helper l with f l ≡ᵢ? (just k)
    ... | yes _ = h l
    ... | no  _ = id


  --fibre-subvec' : (Fin n → Ob) → (Fin n → Maybe Ob)
  --fibre-subvec' v l = f l >>= λ k → {! ≡ᵢ?  !}


module _ {n m o} (f : Fin m → Maybe (Fin o)) (g : Fin n → Maybe (Fin m))
    (k : Fin o)
    -- now we have two vectors
    (v : Fin n → Ob) (v' : Fin m → Ob)
    -- and a way to go between them
    (β : (l : Fin m) → Hom (⨂ $ fibre-subvec g l v) (v' l))
    where
  -- so what do we know

  -- we need the number in both to be the same to use ⨂ so
  h : Hom (⨂ {m} (fibre-subvec f k (λ l → ⨂ $ fibre-subvec g l v))) (⨂ {m} $ fibre-subvec f k v')
  h = subvec₁ f k β

  --these two should be the same, but parenthesized differently
  h₂ : Hom (⨂ $ fibre-subvec (f <=< g) k v) (⨂ $ fibre-subvec f k λ l → ⨂ $ fibre-subvec g l v)
  h₂ = {! !}

  -- todo unfold
  goal : Hom (⨂ {n} (fibre-subvec (f <=< g) k v)) (⨂ {m} (fibre-subvec f k v'))
  goal = h ∘ h₂




open Displayed
E : Displayed Fin∙Sets' o ℓ
E .Ob[_] n = Fin n → Ob
E .Hom[_] {n} {m} f v v' = (k : Fin m) → Hom (⨂ $ fibre-subvec f k v) (v' k)
-- also works? with fewer units but domain varies
--E .Hom[_] {n} {m} f v v' = (k : Fin m) → Hom (⨂ λ l → v (fibre-vec f k l)) (v' k )

E ._∘'_ {a} {b} {c} {x = v} {y = v'} {z = v''} {f = f} {g} α β k = α k ∘ goal f g k v v' β
-- ⨂₁ {vs = {! !}} {vd = where-defined f v'}  {! !} ∘ ?
--E .Hom[_]-set f x y = hlevel 2
--E .id' = id
--E .idr' f' = idr f'
--E .idl' f' = idl f'
--E .assoc' f' g' h' = assoc f' g' h'
--E .hom[_] p f' = f'
--E .coh[_] p f' = refl

private
  open module E = Cat.Displayed.Reasoning E
  open Cat.Displayed.Cocartesian E
  open Cat.Displayed.IsoFibration E
--E ._∘'_ {x = va} {vb} {vc} {f = f} {g} h k l = h l ∘ ? where
  --foo = ⨂₁ {vs = λ j → va (fibre-vec {! (f <=< g) !} (just l) .snd j)} {vd = λ j → vb (fibre-vec f (just l) .snd j)} {! !}
--E .Hom[_] h v v' = Hom (⨂ v) (⨂ v')

--⨂-finset : Finset Ob → Ob
--⨂-finset s = {! !}

module _ {n : Nat} (k : Fin n) (C : E.Ob[ n ]) where
  open Cocartesian-lift

  ρ[k] = ρ[ k ]-kleisli

  ccl : Cocartesian-lift ρ[k] C
  ccl .y' _ = C k
  ccl .lifting = {! !}
  ccl .cocartesian = {! !}



{-
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
-}

```
