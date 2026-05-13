```agda
open import Cat.Prelude
open import Cat.Instances.Dist
```
-->

```agda
module Cat.Instances.Dist.Properties where

{-

module _ (n m : Nat) where
  open Coproduct renaming ([_,_] to [_,_]c)
  open is-coproduct renaming ([_,_] to [_,_]c)
  module sum = Equiv (Finite-coproduct {n} {m})
  Dist-coprods : Coproduct Dist n m
  Dist-coprods .coapex = n + m
  Dist-coprods .ι₁ .map j = just $ sum.to $ inl j
  Dist-coprods .ι₁ .ascending i j p = {! !}
  Dist-coprods .ι₂ .map j = just $ sum.to $ inr j
  Dist-coprods .ι₂ .ascending i j p = {! !}
  Dist-coprods .has-is-coproduct .[_,_]c f g .map = [ f .map , g .map ] ⊙ sum.from
  Dist-coprods .has-is-coproduct .[_,_]c f g .ascending = {! !}
  Dist-coprods .has-is-coproduct .[]∘ι₁ {n} {f} {g} = ext λ j →
    {! !}
  Dist-coprods .has-is-coproduct .[]∘ι₂ = {! !}
  Dist-coprods .has-is-coproduct .unique p p' = {! !}
  --Dist-products .has-is-product .⟨_,_⟩ p1 p2 = {! !}
  --Dist-products .has-is-product .π₁∘⟨⟩ = {! !}
  --Dist-products .has-is-product .π₂∘⟨⟩ = {! !}
  --Dist-products .has-is-product .unique x x' = {! !}

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
