<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Multi.Base
open import Cat.Displayed.Multi.Properties
open import Cat.Instances.Dist
open import Cat.Instances.Dist.Properties
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Closure
open import 1Lab.Reflection

open import Data.Product.NAry
open import Data.Vec.Base
open import Data.Vec.Properties
open import Data.List hiding (lookup-tabulate) renaming (lookup to lookupℓ; tabulate to tabulateℓ)
open import Data.Fin
```
-->

```agda
module Cat.Multi (o ℓ : Level) where
```

# Multicategories {defines=multicategory}

<!--
```agda
open Vec using (lower)
```
-->

```agda

--_![ ] = lookup
record make-multicat (o ℓ : Level) : Type (lsuc (o ⊔ ℓ)) where
  field
    Ob : Type o
    Homl : List Ob → Ob → Type ℓ
    Homl-is-set : ∀ xs y → is-set $ Homl xs y

    id : ∀ (x : Ob) → Homl [ x ] x

  -- ΣHoml = Σ[ xs ∈ List Ob ] Σ[ y ∈ Ob ] Homl xs y

  field
    comp-homl
      : ∀ {n} (xxs : Vec (List Ob) n) (ys : Vec Ob n) (z : Ob)
      → (∀ j → Homl (lookup xxs j) (lookup ys j))
      → Homl (lower ys) z
      → Homl (concat $ lower xxs) z


    idl
      : ∀ {xs y} {h : Homl xs y} →
      PathP (λ i → Homl (singleton-bind xs i) y)
      (comp-homl (singleton <$> vec xs) (vec xs) y
        (λ j → transport (λ i → Homl (map-lookup singleton (vec xs) j (~ i)) (xs ! j)) $ id (xs ! j ))
        h)
      h

    idr
      : ∀ {xs y} {h : Homl xs y} →
      PathP (λ i → Homl (++-idr xs i) y)
        (comp-homl [ xs ] [ y ] y (const→fin1 h) (id y))
        h

private
  homl-set : ∀ {o ℓ} (M : make-multicat o ℓ) {x y} → is-set (M .make-multicat.Homl x y)
  homl-set C = C .make-multicat.Homl-is-set _ _

{-# INLINE make-multicat.constructor #-}
open hlevel-projection
instance
  hlevel-proj-homl : hlevel-projection (quote make-multicat.Homl)
  hlevel-proj-homl .has-level = quote homl-set
  hlevel-proj-homl .get-level _ = pure (lit (nat 2))
  hlevel-proj-homl .get-argument = first-visible




module Make-multicat {o ℓ} (m : make-multicat o ℓ) where
  open make-multicat m
  record MultiHom {n m} (xs : Vec Ob n) (ys : Vec Ob m) (t : ⟨ n ⟩→⟨ m ⟩) : Type (o ⊔ ℓ) where
    field
      idxs : Vec (List $ Fin n) m
      homs : ∀ (k : Fin m) → Homl (lookup xs <$> idxs !v k) (ys !v k)
      -- so now instead of having to deal with paths of objects we only have paths of index lists
      typd : ∀ (k : Fin m) → invs t k ≡ᵢ idxs !v k

      -- but what is the action of t on vecs?
      -- act : (t : ⟨ n ⟩→⟨ m ⟩) -> (v : Vec Ob n) -> Fin m -> List Ob ?
      -- and concat (act vs) ⋖ vs ? (it is le sublist relation)

      -- but given  (doms : Vec (List Ob) m) and t, can you verify that  doms !_ ≡ act t v ? 

      -- probably not an a non-evil way since keeping around Path (List Ob) will have terrible consequences
  open MultiHom

  unquoteDecl H-Level-MultiHom = declare-record-hlevel 2 H-Level-MultiHom (quote MultiHom)

  castHom : ∀ {n m} → {xs : Vec Ob n} {ys : Vec Ob m} (t s : ⟨ n ⟩→⟨ m ⟩) → t ≡ s → MultiHom xs ys t → MultiHom xs ys s
  castHom t s p h .idxs = h .idxs
  castHom t s p h .homs = h .homs
  castHom t s p h .typd k = (Id≃path.from $ sym $ ap invs p ·ₚ k) ∙ᵢ h .typd k 

  open Displayed
  to-displayed : Displayed Dist o (o ⊔ ℓ)
  --to-displayed .Ob[_] 0 = Lift ⊤
  --to-displayed .Ob[_] 1 = Ob
  to-displayed .Ob[_] n = Vec Ob n
  to-displayed .Hom[_] {n} {m} t xs ys = MultiHom xs ys t
  to-displayed .hom[_] = castHom _ _
  to-displayed . Hom[_]-set f x y = hlevel 2
  to-displayed .id' = {!!}
  to-displayed ._∘'_ x x₁ = {!!}
  to-displayed .idr' f' = {!!}
  to-displayed .idl' f' = {!!}
  to-displayed .assoc' f' g' h' = {!!}
  to-displayed. coh[_] p f' = {!!}
{-
  to-displayed .Hom[_]-set {n} {m} f v v' = Π-is-hlevel 2 λ _ → Homl-is-set _ _
  -- do we really want a transp here?

  to-displayed .id' {n} {xs} k = transport (λ j → Homl (lookup xs <$> preimage-id {j = k} (~ j)) (lookup xs k) ) $ id (lookup xs k)
  to-displayed ._∘'_ {a} {b} {c} {xs} {ys} {zs} {f} {g} f' g' k = transport (λ i → Homl (motive₃ i) (lookup zs k)) $ foo
    module multi-comp where

    -- n = ‖ f ⁻¹ k ‖

    mid : Vec (Fin b) ‖ f ⁻¹ k ‖
    mid = vec (preimage-indices f k)


    upper : Vec (List $ Fin a) ‖ f ⁻¹ k ‖
    upper = tabulate λ j → preimage-indices g $ lookup mid j

    --foo : Homl (concat $ _) _
    -- NEED Homl (lookup (lookup xs <<$>> upper) j) (lookup (lookup ys <$> mid) j)
    -- lookup-map ~= Homl (lookup (lookup xs <<$>> upper) j) (lookup ys (lookup mid j))
    -- lookup-map ~= Homl ((lookup xs <$> lookup upper j) (lookup ys (lookup mid j))
    -- lookup-tab ~= Homl ((lookup xs <$> preimage-indices g (lookup mid j)) (lookup ys (lookup mid j))
    -- which we have!!
    g-thing : (j : Fin ‖ f ⁻¹ k ‖) → Homl (lookup xs <$> preimage-indices g (lookup mid j)) (lookup ys (lookup mid j))
    g-thing j = g' (lookup mid j)

    motive₁ : (j : Fin ‖ f ⁻¹ k ‖) → (lookup xs <$> preimage-indices g (lookup mid j)) ≡ lookup (lookup xs <<$>> upper) j
    motive₁ j =
      (lookup xs <$> preimage-indices g (lookup mid j))
        ≡˘⟨ ap (map $ lookup xs) $ lookup-tabulate _ j ⟩
      (lookup xs) <$> (lookup upper j)
        ≡˘⟨ map-lookup (map $ lookup xs) upper j ⟩
      lookup (map (lookup xs) <$> upper) j
        ≡⟨⟩
      lookup (lookup xs <<$>> upper) j ∎

    motive₂ : ∀ j → lookup ys (lookup mid j) ≡ lookup (lookup ys <$> mid) j
    motive₂ j =
      lookup ys (lookup mid j) ≡˘⟨ map-lookup (lookup ys) mid j ⟩
      lookup (lookup ys <$> mid) j ∎

    correct-thing : (j : Fin ‖ f ⁻¹ k ‖) → Homl (lookup (lookup xs <<$>> upper) j) (lookup (lookup ys <$> mid) j)
    correct-thing j = transport (λ i → Homl (motive₁ j i) (motive₂ j i)) $ g' (lookup mid j)

    foo : Homl (concat $ lookup xs <<$>> upper .lower) (lookup zs k)
    foo = comp-homl (lookup xs <<$>> upper) (lookup ys <$> mid) (lookup zs k) (λ j → correct-thing j) (f' k)
    -- but we _need_
    -- Homl (lookup xs <$> preimage-indices (f ∘ g) k) (lookup zs k)
    --
    motive₃ : (concat $ lookup xs <<$>> upper .lower) ≡ (lookup xs <$> preimage-indices (f Dist.∘ g) k)
    motive₃ =
      (concat $ lookup xs <<$>> upper .lower)
        ≡⟨⟩
      (concat $ lookup xs <<$>> (tabulate λ j → (preimage-indices g $ lookup mid j)) .lower)
        ≡⟨ concat-mapp {xs = tabulateℓ λ j → (preimage-indices g $ (preimage-indices f k) ! j)} (lookup xs) ⟩
      lookup xs <$> (concat $ (tabulate λ j → (preimage-indices g $ lookup mid j)) .lower)
        ≡⟨⟩
      lookup xs <$> (concat $ (tabulateℓ λ j → (preimage-indices g $ (preimage-indices f k) ! j)))
        ≡˘⟨ ap (λ c → lookup xs <$> (concat c)) $ map-tabulate (preimage-indices g) (λ j → (preimage-indices f k) ! j) ⟩
      lookup xs <$> (concat $ preimage-indices g <$> (tabulateℓ λ j → (preimage-indices f k) ! j))
        ≡⟨ ap (λ c → Map-List .map (lookup xs) (concat $ Map-List .map (preimage-indices g) c)) $ tabulate-! {xs = preimage-indices f k} ⟩
      lookup xs <$> (concat $ preimage-indices g <$> (preimage-indices f k))
        ≡⟨ ap (λ l → Map-List .map (lookup xs) l) {! !}  -- this is actually the important theorem
         ⟩
      lookup xs <$> preimage-indices (f Dist.∘ g) k
        ∎

  to-displayed .idr' {a} {b} {x = xs} {ys} {f} f' = {! !}
{-
  to-displayed .idr' {a} {b} {x = xs} {ys} {f} f' i k = comp (λ j →
      Homl (multi-comp.motive₃ {a} {a} {b} {xs} {xs} {ys} {f} {Δ-id}
        f' (λ k' → transport (λ j' → Homl (lookup xs <$> preimage-id {a} {k'} (~ j')) (lookup xs k')) (id (lookup {o} xs k'))) k (j)) (lookup ys k)
    ) (∂ i) λ where
    j (i = i0) → transp (λ i₁ → Homl (multi-comp.motive₃ {a} {a} {b} {xs} {xs} {ys} {f} {Δ-id} f' (λ k₁ → transport (λ j₁ → Homl (lookup xs <$> preimage-id (~ j₁)) (lookup xs k₁)) (id (lookup xs k₁))) k i₁) (lookup ys k)) j (multi-comp.foo f' (λ k₁ → transport (λ j₁ → Homl (lookup xs <$> preimage-id (~ j₁)) (lookup xs k₁)) (id (lookup xs k₁))) k)
    j (i = i1) → {! !}
    j (j = i0) → {! !}
  --to-displayed .idr' {x = xs} {ys} f' = ext λ k → {! !}
-}
  to-displayed .idl' f' = {! !}
  to-displayed .assoc' f' g' h' = {! !}
  to-displayed .hom[_] {x = xs} {ys} p f k = transport (λ j → Homl (lookup xs <$> preimage-indices (p j) k) (lookup ys k)) $ f k
  to-displayed .coh[_] {x = xs} {ys} p f i k = transp (λ j → Homl (lookup xs <$> preimage-indices (p (i ∧ j)) k) (lookup ys k)) (~ i) $ f k
  --to-operad : Operad

  open Cat.Displayed.Cocartesian to-displayed public
  open Cat.Displayed.IsoFibration to-displayed

  module _ {m n} (f : ⟨ m ⟩→⟨ n ⟩) (inert : is-inert f) (v : Vec Ob m) where
    open Cocartesian-lift
    open is-cocartesian

    inv : Fin n → Fin m
    inv = inert-inv f inert

    theorem : ∀ k → Path (List $ Fin m) (preimage-indices f k) (singleton $ inv k)
    theorem k = {! !}


    lift-inert : Cocartesian-lift f v
    lift-inert .y' = tabulate λ j → lookup v (inv j)
    lift-inert .lifting k = transport (λ i → Homl (lookup v <$> theorem k (~ i)) (lookup-tabulate (λ z → lookup v (inv z)) k (~ i))) (id $ lookup v $ inv k)
      -- want Homl (lookup v <$> preimage-indices f k) (lookup (tabulate (λ j → lookup v (inv j))) k)
      -- == Homl (lookup v <$> preimage-indices f k) (lookup v (inv k))
      -- ~= Homl (lookup v <$> [ inv k ]) (lookup v (inv k))
      -- <: id {inv k}
    lift-inert .cocartesian .universal m fs k = {! !}
      -- want Goal: Homl (lookup (tabulate (λ j → lookup v (inv j))) <$>  preimage-indices m k) (lookup u' k)
    lift-inert .cocartesian .commutes m h' = {! !}
    lift-inert .cocartesian .unique m' x = {! !}
-}

module _ (M : Multicat o ℓ) where
  open make-multicat
  open module M = Multicat M hiding (Ob)

  to-make-multicat : make-multicat o ℓ
  to-make-multicat .Ob = M.Ob
  to-make-multicat .Homl l x = Hom[ all-one ] (↑ λ j → l ! j) x
  to-make-multicat .Homl-is-set _ _ = hlevel 2
  to-make-multicat .id x = {! !}
  to-make-multicat .comp-homl xxs ys z x x₁ = {! !}
  to-make-multicat .idl = {! !}
  to-make-multicat .idr = {! !}
```
