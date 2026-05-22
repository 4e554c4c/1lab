```agda
open import Cat.Prelude
open import Cat.Instances.Dist
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Product

open import Data.Set.Coequaliser
open import Data.Dec.Base
open import Data.Maybe.Base
open import Data.Maybe.Properties
open import Data.Fin.Closure
open import Cat.Functor.Naturality
open import Data.Fin.Properties
open import Data.Sum
open import Data.Fin.Base renaming (_≤_ to _≤f_; _<_ to _<f_)
open import Data.Nat.Base
open import Data.Nat.Order
open import Data.Nat.Properties
open import Cat.Monoidal.Base
open import Cat.Functor.Bifunctor
```
-->

```agda
module Cat.Instances.Dist.Properties where

open Monoidal-category

module sum {n} {m} = Equiv (Finite-coproduct {n} {m})

open Dist
open make-natural-iso


module _ where
  open Make-bifunctor
  open ⟨_⟩→⟨_⟩
  bb : Make-bifunctor {C = Dist} {D = Dist} {E = Dist}
  bb .F₀ n m = n + m
  bb .lmap {n} {m} {l} f .map k = [ sum.to ⊙ inl <∙> f .map , pure ⊙ sum.to ⊙ inr ] $ sum.from k
  bb .lmap {n} {x} {m} f .ascending j k lt = {! p j k  !} where
    p : ∀ j k → j ≤f k → [ sum.to ⊙ inl <∙> f .map , just ⊙ sum.to ⊙ inr ] (sum.from {n} {m} j) ≲ [ sum.to ⊙ inl <∙> f .map , just ⊙ sum.to ⊙ inr ] (sum.from {n} {m} k)
    p j k lt with sum.from {n} {m} j in w | sum.from {n} {m} k in w'
    ... | inl x | inl y = {! !}
    ... | inl x | inr y = {! !}
    ... | inr x | inl y = {! !} -- impossible ?
    ... | inr x | inr y = {! !}
  bb .rmap {n} {m} {l} g .map y =  [ pure ⊙ sum.to ⊙ inl , sum.to ⊙ inr <∙> g .map ] $ sum.from y
  bb .rmap {n} {m} {l} g .map y =  [ pure ⊙ sum.to ⊙ inl , sum.to ⊙ inr <∙> g .map ] $ sum.from y
  bb .rmap g .ascending j k lt = {! !}
  bb .lmap-id {n} {m} = ext λ k → p k where
   p : ∀ k → [ sum.to ⊙ inl <∙> id .map , just ⊙ sum.to ⊙ inr ] (sum.from {n} {m} k) ≡ just k
   p k with sum.from {n} {m} k in w
   ... | inl x = ap just $ sum.adjunctr $ sym $ Id≃path.to w
   ... | inr x = ap just $ sum.adjunctr $ sym $ Id≃path.to w

  bb .rmap-id {n} {m} = ext λ k → p k where
   p : ∀ k → [ pure ⊙ sum.to ⊙ inl , sum.to ⊙ inr <∙> id .map ] (sum.from {m} {n} k) ≡ just k
   p k with sum.from {m} {n} k in w
   ... | inl x = ap just $ sum.adjunctr $ sym $ Id≃path.to w
   ... | inr x = ap just $ sum.adjunctr $ sym $ Id≃path.to w

  bb .lmap-∘ {a} {b} {c} {x} f g = ext λ k → {! !} where
    p : ∀ k → bb .lmap {x = x} (f ∘ g) · k ≡ (bb .lmap f ∘ lmap bb g) · k
    p k with sum.from {a} {x} k in w
    ... | inl x = {! !}
    ... | inr x = {! !}
  bb .rmap-∘ f g = ext λ k → {! !}
  bb .lrmap  f g = ext λ k → {! !}

blah : Monoidal-category Dist
blah .-⊗- = make-bifunctor bb

  --lem : ∀ {P : ∀ {n m ℓ} (k : Fin (n + m)) → (Fin n ⊎ Fin m) → Type ℓ}
  --    → (∀ j → P (inl j))
  --    → (∀ j → P (inl k))
  --    → ∀ x → P x

blah .Unit = 0
blah .unitor-l = to-natural-iso record where
      eta n = id
      inv n = id
      eta∘inv n = trivial!
      inv∘eta n = trivial!
      natural n m f = ext λ k → {! !}
blah .unitor-r = to-natural-iso record where
      eta n = cast-id $ sym $ +-zeror n
      inv n = cast-id $ +-zeror n
      eta∘inv n = trivial!
      inv∘eta n = trivial!
      natural n m f = {! !}
blah .associator = to-natural-iso record where
      eta (j , k , l) = cast-id $ sym $ +-associative j k l
      inv (j , k , l) = cast-id $ +-associative j k l
      eta∘inv n = trivial!
      inv∘eta n = trivial!
      natural (n , m , l) (n' , m' , l') (f , g , h) = ext λ { k → {! !} }
--iso→isoⁿ (λ (j , k , l) → path→iso $ sym $ +-associative j k l) {! !}
blah .triangle = ext λ k → {! !}
blah .pentagon = ext λ k → {! !}

{-
  open Coproduct renaming ([_,_] to [_,_]c)
  open is-coproduct renaming ([_,_] to [_,_]c)
  module sum = Equiv (Finite-coproduct {n} {m})
  {-# TERMINATING #-}
  Dist-coprods : Coproduct Dist n m
  Dist-coprods .coapex = n + m
  Dist-coprods .ι₁ .map j = just $ sum.to $ inl j
  Dist-coprods .ι₁ .ascending i j lt = j≲j $ F+-monotonic.to-inl {n} {m} i j lt
  Dist-coprods .ι₂ .map j = just $ sum.to $ inr j
  Dist-coprods .ι₂ .ascending i j lt = j≲j $ F+-monotonic.to-inr {n} {m} i j lt
  Dist-coprods .has-is-coproduct .[_,_]c f g .map = [ f .map , g .map ] ⊙ sum.from
  Dist-coprods .has-is-coproduct .[_,_]c f g .ascending x y p = {! !}
  Dist-coprods .has-is-coproduct .[]∘ι₁ {n} {f} {g} = ext λ j → ap [ f .map , g .map ] (sum.η (inl j))
  Dist-coprods .has-is-coproduct .[]∘ι₂ {_} {f} {g} = ext λ j → ap [ f .map , g .map ] (sum.η (inr j))
  Dist-coprods .has-is-coproduct .unique {k} {in0} {in1} {other} p p' = ext λ j → pf j where
    pf : ∀ j → map other j ≡ ([ in0 .map , in1 .map ] ⊙ sum.from) j
    pf j with sum.from j in w
    ... | inl x = ap· other (sym $ sum.adjunctr $ sym $ Id≃path.to w) ∙ p ·ₚ x
    ... | inr x = ap· other (sym $ sum.adjunctr $ sym $ Id≃path.to w) ∙ p' ·ₚ x
  --Dist-products .has-is-product .⟨_,_⟩ p1 p2 = {! !}
  --Dist-products .has-is-product .π₁∘⟨⟩ = {! !}
  --Dist-products .has-is-product .π₂∘⟨⟩ = {! !}
  --Dist-products .has-is-product .unique x x' = {! !}

  open Product
  open is-product
  Dist-prods : Product Dist n m
  Dist-prods .apex = n + m
  Dist-prods .π₁ .map (fin j ⦃ p ⦄) with holds? (j < n)
  ... | yes a = just $ fin j ⦃ a ⦄
  ... | no ¬a = nothing
  Dist-prods .π₁ .ascending i j lt = {! !}
  Dist-prods .π₂ .map (fin j ⦃ p ⦄) with holds? (j < n)
  ... | yes a = nothing
  ... | no ¬a = just $ fin (j - n) ⦃ {! !} ⦄
  Dist-prods .π₂ .ascending i j lt = {! !}
  Dist-prods .has-is-product .⟨_,_⟩ p1 p2 = {! !}

module _ (f : ⟨ n ⟩→⟨ m ⟩) (j : Fin m) where
  --List⟨_⁻¹_⟩ : List (fibre (f .map) (just j))
  --List⟨_⁻¹_⟩ = {! !}
  --module listing = Listing List⟨_⁻¹_⟩

  --postulate
  --  listing-sorted : is-sorted vals

  preimage-indices : List (Fin n)
  preimage-indices = filter (λ i → Dec→Bool $ f · i ≡ᵢ? just j) (all-fin n)

  ‖_⁻¹_‖ : Nat
  ‖_⁻¹_‖ = length preimage-indices

  preimage-finmap : Fin ‖_⁻¹_‖ → Fin n
  preimage-finmap j = preimage-indices ! j


  premimage-indices-ordered : ∀ (j k : Fin ‖_⁻¹_‖) → (j < k) → (preimage-indices ! j) < (preimage-indices ! k)
  premimage-indices-ordered = filter-sorted {R = _<_} (all-fin n) _ all-fin-sorted .is-sorted.sorted
    where
      open is-sorted
      all-fin-index : ∀ {n} j → (all-fin n ! j) .lower ≡ᵢ j .lower
      all-fin-index {suc n} i with fin-view i
      ... | suc i = {! !}
      ... | zero with fin-view j
      ...   | zero = reflᵢ
      ...   | suc j = reflᵢ

      all-fin-sorted : ∀ {n} → is-sorted _<_ (all-fin n)
      all-fin-sorted .sorted i j lt = subst₂ᵢ _<n_ (symᵢ $ all-fin-index i) (symᵢ $ all-fin-index j) lt

  fibre→preimage-mem : (p : fibreᵢ (f .map) (just j)) → (fst p ∈ preimage-indices)
  fibre→preimage-mem (k , pf) = member-filter.from $ SoDec pf , Listing-Fin .Listing.has-member k .centre


sorted-mem-ext
  : ∀ {n} {xs ys : List $ Fin n} → (xs-sorted : is-sorted _<_ xs) (ys-sorted : is-sorted _<_ ys) →
  ((x : Fin n) → x ∈ xs → x ∈ ys) → ((y : Fin n) → y ∈ ys → y ∈ xs) → xs ≡ᵢ ys
sorted-mem-ext {n} {xs = []}     {[]}     _ _ x→y y→x = reflᵢ
sorted-mem-ext {n} {xs = x ∷ xs} {[]}     _ _ x→y y→x with () ← x→y x (here reflᵢ)
sorted-mem-ext {n} {xs = []}     {y ∷ ys} _ _ x→y y→x with () ← y→x y (here reflᵢ)
sorted-mem-ext {n} {xs = x ∷ xs} {y ∷ ys} xs-sorted ys-sorted x→y y→x with (x→y x $ here reflᵢ) | (y→x y $ here reflᵢ)
... | here p | _ = ap-∷ᵢ p $ sorted-mem-ext (tail-sorted xs-sorted) (tail-sorted ys-sorted) x→y' y→x' where
  x→y' : (x : Fin n) → x ∈ₗ xs → x ∈ ys
  x→y' x mem with x→y x (there mem)
  ... | here p' = absurd $ᵢ <-not-equal (mem→rel xs-sorted mem) $ Id≃path.to $ apᵢ lower $ p ∙ᵢ (symᵢ p')
  ... | there p = p

  y→x' : (y : Fin n) → y ∈ₗ ys → y ∈ xs
  y→x' y mem with y→x y (there mem)
  ... | here p' = absurd $ᵢ <-not-equal (mem→rel ys-sorted mem) $ Id≃path.to $ apᵢ lower $ symᵢ $ p' ∙ᵢ p
  ... | there p = p

... | there _ | here p = ap-∷ᵢ (symᵢ p) $ sorted-mem-ext (tail-sorted xs-sorted) (tail-sorted ys-sorted) x→y' y→x' where
  x→y' : (x : Fin n) → x ∈ₗ xs → x ∈ ys
  x→y' x mem with x→y x (there mem)
  ... | here p' = absurd $ᵢ <-not-equal (mem→rel xs-sorted mem) $ Id≃path.to $ apᵢ lower $ symᵢ $ p' ∙ᵢ p
  ... | there p = p

  y→x' : (y : Fin n) → y ∈ₗ ys → y ∈ xs
  y→x' y mem with y→x y (there mem)
  ... | here p' = absurd $ᵢ <-not-equal (mem→rel ys-sorted mem) $ Id≃path.to $ apᵢ lower $ p ∙ᵢ (symᵢ p')
  ... | there p = p

... | there pf1 | there pf2 = absurd $ᵢ <-asym (mem→rel ys-sorted pf1) (mem→rel xs-sorted pf2)


module _ (g : ⟨ k ⟩→⟨ n ⟩) (f : ⟨ n ⟩→⟨ m ⟩) (j : Fin m) where

  open is-sorted
  concat-strictly-sorted : is-sorted _<_ $ concat $ preimage-indices g <$> preimage-indices f j
  concat-strictly-sorted .sorted i j lt = {! !}

  lem₀ : (k : Fin k) → k ∈ preimage-indices (f Dist.∘ g) j  → k ∈ (concat $ preimage-indices g <$> preimage-indices f j)
  lem₀ k p = {! !}

  lem₁ : (k : Fin k) → k ∈ (concat $ preimage-indices g <$> preimage-indices f j) → k ∈ preimage-indices (f Dist.∘ g) j
  lem₁ k p with member→concat-member k (preimage-indices g <$> preimage-indices f j) p
  ... | inner , m , s = fibre→preimage-mem (f Dist.∘ g) j $ k , {! !}

  concat-preimages : preimage-indices (f Dist.∘ g) j ≡ (concat $ preimage-indices g <$> preimage-indices f j)
  concat-preimages = {! sorted-mem-ext !}
  {-
    filter (λ i → Dec→Bool $ (g .map i >>= f .map) ≡ᵢ? just j) (all-fin k)
    ≡⟨ {! !} ⟩
    (concat $
    (λ j' → filter (λ i → Dec→Bool $ (map g i ≡ᵢ? just j')) (all-fin k))
    <$> filter (λ i → Dec→Bool (map f i ≡ᵢ? just j)) (all-fin n))
    ≡⟨ {! !} ⟩
    (concat $
    (λ j' → filter (λ i → Dec→Bool $ (map g i ≡ᵢ? just j')) (all-fin k))
    <$> filter (λ i → Dec→Bool (map f i ≡ᵢ? just j)) (all-fin n))
    ≡⟨⟩
    (concat $ preimage-indices g <$> preimage-indices f j) ∎
-}

{-


  index_image : Fin ‖_⁻¹_‖ → Fin n
  index_image k = fst $ listing.univ ! k
-}

preimage-id : ∀ {n} → {j : Fin n} → preimage-indices Δ-id j ≡  j ∷ []
-- for this we need to prove that [ j , pf ] is a listing, and that listings are
-- unique but unique listings are really a poor choice for this whole situation
  lem₁ k p with member→concat-member k (preimage-indices g <$> preimage-indices f j) p
  ... | inner , m , s = fibre→preimage-mem (f Dist.∘ g) j $ k , {! !}

  concat-preimages : preimage-indices (f Dist.∘ g) j ≡ (concat $ preimage-indices g <$> preimage-indices f j)
  concat-preimages = {! sorted-mem-ext !}
  {-
    filter (λ i → Dec→Bool $ (g .map i >>= f .map) ≡ᵢ? just j) (all-fin k)
    ≡⟨ {! !} ⟩
    (concat $
    (λ j' → filter (λ i → Dec→Bool $ (map g i ≡ᵢ? just j')) (all-fin k))
    <$> filter (λ i → Dec→Bool (map f i ≡ᵢ? just j)) (all-fin n))
    ≡⟨ {! !} ⟩
    (concat $
    (λ j' → filter (λ i → Dec→Bool $ (map g i ≡ᵢ? just j')) (all-fin k))
    <$> filter (λ i → Dec→Bool (map f i ≡ᵢ? just j)) (all-fin n))
    ≡⟨⟩
    (concat $ preimage-indices g <$> preimage-indices f j) ∎
-}

{-


  index_image : Fin ‖_⁻¹_‖ → Fin n
  index_image k = fst $ listing.univ ! k
-}

preimage-id : ∀ {n} → {j : Fin n} → preimage-indices Δ-id j ≡  j ∷ []
-- for this we need to prove that [ j , pf ] is a listing, and that listings are
-- unique but unique listings are really a poor choice for this whole situation
  lem₁ k p with member→concat-member k (preimage-indices g <$> preimage-indices f j) p
  ... | inner , m , s = fibre→preimage-mem (f Dist.∘ g) j $ k , {! !}

  concat-preimages : preimage-indices (f Dist.∘ g) j ≡ (concat $ preimage-indices g <$> preimage-indices f j)
  concat-preimages = {! sorted-mem-ext !}
  {-
    filter (λ i → Dec→Bool $ (g .map i >>= f .map) ≡ᵢ? just j) (all-fin k)
    ≡⟨ {! !} ⟩
    (concat $
    (λ j' → filter (λ i → Dec→Bool $ (map g i ≡ᵢ? just j')) (all-fin k))
    <$> filter (λ i → Dec→Bool (map f i ≡ᵢ? just j)) (all-fin n))
    ≡⟨ {! !} ⟩
    (concat $
    (λ j' → filter (λ i → Dec→Bool $ (map g i ≡ᵢ? just j')) (all-fin k))
    <$> filter (λ i → Dec→Bool (map f i ≡ᵢ? just j)) (all-fin n))
    ≡⟨⟩
    (concat $ preimage-indices g <$> preimage-indices f j) ∎
-}

{-


  index_image : Fin ‖_⁻¹_‖ → Fin n
  index_image k = fst $ listing.univ ! k
-}

preimage-id : ∀ {n} → {j : Fin n} → preimage-indices Δ-id j ≡  j ∷ []
-- for this we need to prove that [ j , pf ] is a listing, and that listings are
-- unique but unique listings are really a poor choice for this whole situation
-- we should be using Finite A and proving that if a total order exists on A, then
-- there is a canonical map Finite A -> Listing A given by sort!
-- then if we prove that [ j , pf ] is a sorted (obviously) listing, then it is
-- canonical.
preimage-id {suc n} {j} with fin-view j
... | zero = ap-∷ refl {! !}
... | suc j = want
  where
    rec : preimage-indices Δ-id j ≡ j ∷ []
    rec = preimage-id {n} {j}
    want : (filter _ (fsuc <$> all-fin n)) ≡ (fsuc j) ∷ []
    want = {! !}
-}
```
