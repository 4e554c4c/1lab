
```agda
{-# OPTIONS --allow-unsolved-metas #-}

--open import Data.Product.NAry
open import Cat.Instances.Simplex
open import Cat.Morphism.Class
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Diagram.Product
open import Cat.Diagram.Zero
open import Cat.Functor.Base
open import Cat.Prelude
open import Cat.Gaunt

open import Cat.Diagram.Product
open import Cat.Diagram.Coproduct


open import Data.Fin.Closure
open import Data.Maybe.Base
open import Data.Maybe.Properties
open import Data.Nat.Order
open import Data.Bool
open import Data.Nat using (H-Level-Nat; s≤s; 0≤x) renaming (_≤_ to _≤n_; _<_ to _<n_)
open import Data.Dec.Base
open import Data.Sum.Base --hiding ([_,_])
open import Data.List
open import Data.Fin
open import Data.Fin.Monotone
open import Data.List.Sorted
open import Data.Irr

import Cat.Reasoning
import Cat.Morphism

open import Meta.Idiom

open Functor
```
-->

```agda
module Cat.Instances.Dist where

private variable
  n m k : Nat

module _ {n : Nat} where
  data _≲_ : Maybe (Fin n) → Maybe (Fin n) → Type where
    n≲n : nothing ≲ nothing
    n≲j : ∀ {x} → nothing ≲ just x
    j≲n : ∀ {x} → just x ≲ nothing
    j≲j : ∀ {x y} → x ≤ y → just x ≲ just y

  ≲-is-prop : ∀ {x y} → is-prop (x ≲ y)
  ≲-is-prop n≲n     n≲n     = refl
  ≲-is-prop n≲j     n≲j     = refl
  ≲-is-prop j≲n     j≲n     = refl
  ≲-is-prop (j≲j p) (j≲j q) = ap j≲j (hlevel 1 p q)

  instance
    H-Level-≲ : ∀ {m x y} → H-Level (x ≲ y) (suc m)
    H-Level-≲ = prop-instance ≲-is-prop

  n≲x : ∀ {x} → nothing ≲ x
  n≲x {nothing} = n≲n
  n≲x {just x} = n≲j

  x≲n : ∀ {x} → x ≲ nothing
  x≲n {nothing} = n≲n
  x≲n {just x} = j≲n

record ⟨_⟩→⟨_⟩ (n m : Nat) : Type where
  constructor sasc
  field
    map       : Fin n → Maybe (Fin m)
    ascending : (x y : Fin n) → x ≤ y → map x ≲ map y

unquoteDecl H-Level-⟨⟩→⟨⟩ = declare-record-hlevel 2 H-Level-⟨⟩→⟨⟩ (quote ⟨_⟩→⟨_⟩)

open ⟨_⟩→⟨_⟩

⟨⟩→⟨⟩-path
  : ∀ {n m : Nat} {f g : ⟨ n ⟩→⟨ m ⟩}
  → (∀ x → f .map x ≡ g .map x)
  → f ≡ g
⟨⟩→⟨⟩-path p i .map x = p x i
⟨⟩→⟨⟩-path {f = f} {g} p i .ascending x y w =
  is-prop→pathp (λ j → ≲-is-prop {_} {p x j} {p y j})
    (f .ascending x y w) (g .ascending x y w) i

instance
  Funlike-⟨⟩→⟨⟩ : ∀ {n m} → Funlike ⟨ n ⟩→⟨ m ⟩ (Fin n) λ _ → Maybe (Fin m)
  Funlike-⟨⟩→⟨⟩ = record { _·_ = ⟨_⟩→⟨_⟩.map }

  Extensional-⟨⟩→⟨⟩ : ∀ {n m} → Extensional ⟨ n ⟩→⟨ m ⟩ lzero
  Extensional-⟨⟩→⟨⟩ {n} .Pathᵉ   f g = ∀ (j : Fin n) → (f · j) ≡ (g · j)
  Extensional-⟨⟩→⟨⟩ .reflᵉ _ j = refl
  Extensional-⟨⟩→⟨⟩ .idsᵉ .to-path = ⟨⟩→⟨⟩-path
  Extensional-⟨⟩→⟨⟩ .idsᵉ .to-path-over p = is-prop→pathp (λ i → hlevel 1) (λ j → refl) p

comp-Δ  : ∀{n m k} (f : ⟨ m ⟩→⟨ k ⟩) (g : ⟨ n ⟩→⟨ m ⟩) → ⟨ n ⟩→⟨ k ⟩
comp-Δ f g .map = f .map <=< g .map
comp-Δ f g .ascending x y p with g .map x | g .map y | g .ascending x y p
... | nothing | _       | _     = n≲x
... | just _  | nothing | _     = x≲n
... | just x  | just y  | j≲j q = f .ascending x y q

Δ-id : ∀ {n} → ⟨ n ⟩→⟨ n ⟩
Δ-id .map = just
Δ-id .ascending _ _ = j≲j

all-one : ∀ {n} → ⟨ n ⟩→⟨ 1 ⟩
all-one .map _ = just 0
all-one .ascending _ _ _ = j≲j 0≤x

-- a function is 'inert' if it's an equivalence to its defined domain
is-inert : ∀ {n m} → ⟨ n ⟩→⟨ m ⟩ → Type
is-inert (sasc f _) = ∀ x → is-contr (fibre f (just x))

ρ[_] : ∀ {n} → Fin n → ⟨ n ⟩→⟨ 1 ⟩
ρ[ k ] .map x = ifᵈ (x ≡ᵢ? k) then just 0 else nothing
ρ[ k ] .ascending x y p with (x ≡ᵢ? k) | (y ≡ᵢ? k)
... | no ¬a | q = n≲x
... | yes a | yes b = j≲j 0≤x
... | yes a | no ¬b = x≲n

ρ-inert : ∀ {n k} → is-inert {n} ρ[ k ]
ρ-inert {n} {k} d .centre .fst = k
ρ-inert {n} {k} d .centre .snd with fin-view d
... | zero = refl
ρ-inert {n} {k} d .paths (k' , p) = Σ-prop-path (λ j → hlevel 1) (sym pf) where
  pf : k' ≡ k
  pf with (k' ≡ᵢ? k)
  pf | yes q = Id≃path.to q
  pf | no ¬q = absurd $ᵢ nothing≠just p

inert-inv : ∀ {n m} → {f : ⟨ n ⟩→⟨ m ⟩} → is-inert f → (Fin m → Fin n)
inert-inv inert k = inert k .centre .fst

inert-inv-inj : ∀ {n m} → (f : ⟨ n ⟩→⟨ m ⟩) → (inert : is-inert f) → injective (inert-inv {f = f} inert)
inert-inv-inj f inert {i} {j} p = just-inj $ sym (inert i .centre .snd) ∙ ap· f p ∙ inert j .centre .snd

inert-lt : ∀ {n m} → (f : ⟨ n ⟩→⟨ m ⟩) → is-inert f → m ≤n n
inert-lt f inert = Fin-injection→lt (inert-inv {f = f} inert) (inert-inv-inj f inert)

-- instead of negating the fibre here, we use a slightly more constructive, equivalent definition
is-active : ∀ {n m} → ⟨ n ⟩→⟨ m ⟩ → Type
is-active {n} {m} f = ∀ (j : Fin n) → is-just (f · j)

lift-active : (f : ⟨ n ⟩→⟨ m ⟩) → (is-active f) → Fin n → Fin m
lift-active f active k = from-just! (f · k) (active k)

Dist : Precategory lzero lzero
Dist .Precategory.Ob = Nat
Dist .Precategory.Hom n m = ⟨ n ⟩→⟨ m ⟩
Dist .Precategory.Hom-set _ _ = hlevel 2
Dist .Precategory.id = Δ-id
Dist .Precategory._∘_ = comp-Δ
Dist .Precategory.idr f = ext λ j → refl
Dist .Precategory.idl f = ext p where
  p : (j : Fin _) → (f · j >>= just) ≡ f · j
  p j with f .map j
  ... | just x = refl
  ... | nothing = refl
Dist .Precategory.assoc f g h = ext p where
  p : (j : Fin _) → (h .map j >>= g .map >>= f .map) ≡ (h .map j >>= (g .map >=> f .map))
  p j with h · j
  ... | nothing = refl
  ... | just x with g · x
  ...   | nothing = refl
  ...   | just y  = refl

open module Dist = Cat.Reasoning Dist

inert-ρ : ∀ {n m k} → {f : ⟨ n ⟩→⟨ m ⟩} → (ine : is-inert f) → ρ[ k ] ∘ f ≡ ρ[ inert-inv {f = f} ine k ]
inert-ρ {k = k} {f = f} f-inert = ext pf
  where
  pf : ∀ k' → (ρ[ k ] ∘ f) · k' ≡ ρ[ inert-inv {f = f} f-inert k ] · k'
  pf k' with k' ≡ᵢ? inert-inv {f = f} f-inert k  --| (Id≃path.to $ f-inert .centre .snd k)
  ... | no ¬a = {! !}
  ... | yes a with Id≃path.from $ f-inert k .centre .snd
  ... | blah = {! !}


Inert : Arrows Dist lzero
Inert .arrows = is-inert
Inert .is-tr = hlevel 1

Active : Arrows Dist lzero
Active .arrows = is-active
Active .is-tr = hlevel 1

open Cat.Morphism.is-invertible
is-iso→Inert : ∀ {a b} {f : ⟨ a ⟩→⟨ b ⟩} → Dist.is-invertible f → f ∈ Inert
is-iso→Inert iv n .centre with iv .inv · n | iv .invl ·ₚ n
... | nothing | q = absurd $ᵢ nothing≠just q
... | just k | q = k , q
is-iso→Inert {f = f} iv n .paths p with iv .inv · n | iv .invl ·ₚ n
... | nothing | q = absurd $ᵢ nothing≠just q
... | just k | q = {! p .snd !}

is-iso→Active : ∀ {a b} {f : ⟨ a ⟩→⟨ b ⟩} → Dist.is-invertible f → f ∈ Active
is-iso→Active {f = f} iv n with f · n | ap (λ f → f .map n) (iv .invr)
... | nothing | q = absurd $ᵢ nothing≠just q
... | just k | q = lift oh

is-iso→prop : (f g : n ≅ m) → f ≡ g
is-iso→prop f g = Dist.≅-path (ext pf) where
  module f = _≅_ f
  module g = _≅_ g

  f-invertible : is-invertible f.to
  f-invertible = inverses→invertible f.inverses
  g-invertible : is-invertible g.to
  g-invertible = inverses→invertible g.inverses

  f-active = is-iso→Active f-invertible
  g-active = is-iso→Active g-invertible

  f⁻¹-active = is-iso→Active $ f-invertible invertible⁻¹
  g⁻¹-active = is-iso→Active $ g-invertible invertible⁻¹

  f^ = lift-active f.to f-active
  g^ = lift-active g.to g-active

  open is-iso
  f^-iso : is-iso f^
  f^-iso .from = lift-active f.from f⁻¹-active
  f^-iso .rinv j with (f.from · j) | (f.invl ·ₚ j) |  f⁻¹-active j
  ... | just x | p | _ with (f.to · x) |  f-active x
  ... | just y | _ = just-inj p
  f^-iso .linv j with (f.to · j) | (f.invr ·ₚ j) |  f-active j
  ... | just x | p | _ with (f.from · x) |  f⁻¹-active x
  ... | just y | _ = just-inj p

  g^-iso : is-iso g^
  g^-iso .from = lift-active g.from g⁻¹-active
  g^-iso .rinv j with (g.from · j) | (g.invl ·ₚ j) |  g⁻¹-active j
  ... | just x | p | _ with (g.to · x) |  g-active x
  ... | just y | _ = just-inj p
  g^-iso .linv j with (g.to · j) | (g.invr ·ₚ j) |  g-active j
  ... | just x | p | _ with (g.from · x) |  g⁻¹-active x
  ... | just y | _ = just-inj p

  f^-mon : is-monotone f^
  f^-mon i j le with (f.to · i) | (f.to · j) | f-active i | f-active j | (f.to .ascending i j le)
  ... | just x | just x₁ | a | b | j≲j p = p

  g^-mon : is-monotone g^
  g^-mon i j le with (g.to · i) | (g.to · j) | g-active i | g-active j | (g.to .ascending i j le)
  ... | just x | just x₁ | a | b | j≲j p = p

  suffices : f^ ≡ g^
  suffices = mon-skeletal _ _ f^-iso g^-iso f^-mon g^-mon

  pf : ∀ j → f · j ≡ g · j
  pf j with (f · j) | (g · j) | f-active j | g-active j | happly suffices j
  ... | just x | just y | _ | _ | p = ap just p

open is-gaunt
open Cat.Morphism
Dist-gaunt : is-gaunt Dist
Dist-gaunt .has-category .to-path {n} {m} i = ≤-antisym  (p $ i Dist.Iso⁻¹) (p i) where
  p : ∀ {n m} → n Dist.≅ m → m ≤n n
  p q = inert-lt (q ._≅_.to) $ is-iso→Inert $ Dist.iso→invertible q
Dist-gaunt .has-category .to-path-over p = is-prop→pathp (λ i a b → is-iso→prop a b) Dist.id-iso p
Dist-gaunt .has-strict = hlevel 2

Dist-cat : is-category Dist
Dist-cat = Dist-gaunt .has-category

-- does it have products?

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

  --preimage-mem→fibre : ∀ {k} → (k ∈ₗ preimage-indices) → (fibreᵢ (f .map) (just j))
  --preimage-mem→fibre mem = ?

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

```
