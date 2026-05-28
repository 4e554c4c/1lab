```agda
open import Cat.Instances.Simplex
open import Cat.Diagram.Zero
open import Cat.Morphism.Lifts
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Morphism.Class
open import Cat.Morphism.Factorisation
open import Cat.Morphism.Factorisation.Orthogonal
open import Cat.Diagram.Zero
open import Cat.Functor.Base
open import Cat.Prelude
open import Cat.Gaunt
open import Data.Nat.Order
open import Data.Nat.Properties


open import Data.Fin.Closure
open import Data.Maybe.Base
open import Data.Maybe.Properties
open import Data.Nat.Order
open import Data.Bool
open import Data.Nat -- using (H-Level-Nat; s≤s; 0≤x ; ≤-trans)
open import Data.Dec.Base
open import Data.Fin renaming (_≤_ to _≤f_; _<_ to _<f_)
open import Data.Fin.Monotone

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
    j≲j : ∀ {x y} → x ≤f y → just x ≲ just y

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

0≲x : ∀ {x : Maybe $ Fin $ suc n} → (just fzero) ≲ x
0≲x {_} {nothing} = j≲n
0≲x {_} {just x} = j≲j 0≤x

record ⟨_⟩→⟨_⟩ (n m : Nat) : Type where
  constructor sasc
  field
    map       : Fin n → Maybe (Fin m)
    ascending : (x y : Fin n) → x ≤f y → map x ≲ map y

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
ρ-inert {n} {k} d .paths (k' , p) = Σ-prop-path! (sym pf) where
  pf : k' ≡ k
  pf with (k' ≡ᵢ? k)
  pf | yes q = Id≃path.to q
  pf | no ¬q = absurd $ᵢ nothing≠just p

inert-inv : ∀ {n m} → {f : ⟨ n ⟩→⟨ m ⟩} → is-inert f → (Fin m → Fin n)
inert-inv inert k = inert k .centre .fst

inert-inv-inj : ∀ {n m} → (f : ⟨ n ⟩→⟨ m ⟩) → (inert : is-inert f) → injective (inert-inv {f = f} inert)
inert-inv-inj f inert {i} {j} p = just-inj $ sym (inert i .centre .snd) ∙ ap· f p ∙ inert j .centre .snd

inert-lt : ∀ {n m} → (f : ⟨ n ⟩→⟨ m ⟩) → is-inert f → m ≤ n
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

Inert : Arrows Dist lzero
Inert .arrows = is-inert
Inert .is-tr = hlevel 1

Active : Arrows Dist lzero
Active .arrows = is-active
Active .is-tr = hlevel 1

inert-comp-ρ : ∀ {n m k} → {f : ⟨ n ⟩→⟨ m ⟩} → (ine : is-inert f) → ρ[ k ] ∘ f ≡ ρ[ inert-inv {f = f} ine k ]
inert-comp-ρ {k = k} {f = f} f-inert = ext pf where
  pf : ∀ k' → (ρ[ k ] ∘ f) · k' ≡ ρ[ inert-inv {f = f} f-inert k ] · k'
  pf k' with k' ≡ᵢ? inert-inv {f = f} f-inert k
  pf k' | no ¬a with f · k' in w
  pf k' | no ¬a | nothing = refl
  pf k' | no ¬a | just x with x ≡ᵢ? k
  pf k' | no ¬a | just x | yes reflᵢ = absurd
    $ᵢ ¬a $ Id≃path.from $ sym $ ap fst
    $ f-inert x .paths $ k' , Id≃path.to w
  pf k' | no ¬a | just x | no ¬p = refl
  pf k' | yes a with f · k' in w
  pf k' | yes a | nothing = absurd $ᵢ nothing≠just
    $ sym (Id≃path.to w) ∙∙ ap· f (Id≃path.to a) ∙∙ f-inert k .centre .snd
  pf k' | yes a | just x with x ≡ᵢ? k
  pf k' | yes a | just x | yes b = refl
  pf k' | yes a | just x | no ¬b = absurd $ᵢ ¬b $ Id≃path.from l2 where

    l1 : f-inert x .centre .fst ≡ f-inert k .centre .fst
    l1 = (ap fst $ f-inert x .paths $ k'  , Id≃path.to w) ∙ Id≃path.to a

    l2 : x ≡ k
    l2 = just-inj $ sym (f-inert x .centre .snd) ∙∙ ap· f l1 ∙∙ f-inert k .centre .snd

open Cat.Morphism.is-invertible

is-iso→Inert : ∀ {a b} {f : ⟨ a ⟩→⟨ b ⟩} → Dist.is-invertible f → f ∈ Inert
is-iso→Inert iv n .centre with iv .inv · n | iv .invl ·ₚ n
... | nothing | q = absurd $ᵢ nothing≠just q
... | just k | q = k , q
is-iso→Inert {a} {b} {f = f} iv n .paths p with iv .inv · n | iv .invl ·ₚ n
... | nothing | q = absurd $ᵢ nothing≠just q
... | just k | q = Σ-prop-path! $ f'.injective (just-inj $ sym f≡f' ∙ q ∙ sym (p .snd) ∙ f≡f') where
  f' : Fin a → Fin b
  f' k with f · k | iv .invr ·ₚ k
  f' k | nothing | p = absurd $ᵢ nothing≠just p
  f' k | just x | p = x

  f≡f' : ∀ {k} → f · k ≡ just (f' k)
  f≡f' {k} with f · k | iv .invr ·ₚ k
  f≡f' {k} | nothing | p = absurd $ᵢ nothing≠just p
  f≡f' {k} | just x | _ = refl

  f'-iso : is-iso f'
  f'-iso .is-iso.from k with iv .inv · k | iv .invl ·ₚ k
  ... | nothing | p = absurd $ᵢ nothing≠just p
  ... | just x | p = x
  f'-iso .is-iso.rinv k with iv .inv · k | iv .invl ·ₚ k
  ... | nothing | p = absurd $ᵢ nothing≠just p
  ... | just l | p with f · l | iv .invr ·ₚ l
  ... | nothing | p = absurd $ᵢ nothing≠just p
  ... | just m | _ = just-inj p
  f'-iso .is-iso.linv l with f · l | iv .invr ·ₚ l
  ... | nothing | p = absurd $ᵢ nothing≠just p
  ... | just k | p with iv .inv · k | iv .invl ·ₚ k
  ... | nothing | p = absurd $ᵢ nothing≠just p
  ... | just m | _ = just-inj p

  module f' = Equiv (f' , is-iso→is-equiv f'-iso)

is-inert-∘ : ∀ {a b c} {f : ⟨ b ⟩→⟨ c ⟩} {g : ⟨ a ⟩→⟨ b ⟩}
  → is-inert f → is-inert g → is-inert (f ∘ g)
is-inert-∘ {f = f} {g} if ig j .centre .fst = ig (if j .centre .fst) .centre .fst
is-inert-∘ {f = f} {g} if ig j .centre .snd = ap (_>>= f .map) (ig (if j .centre .fst) .centre .snd) ∙ if j .centre .snd
is-inert-∘ {f = f} {g} if ig j .paths (k , p) = Σ-prop-path! pf where
  pf : ig (if j .centre .fst) .centre .fst ≡ k
  pf with g · k in w
  ... | nothing with () ← nothing≠just p
  ... | just x = ap fst $ ig (if j .centre .fst) .paths $ k ,_ $ sym $
    (ap just $ ap fst $ if j .paths $ x , p) ∙ (sym $ Id≃path.to w)

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
  p : ∀ {n m} → n Dist.≅ m → m ≤ n
  p q = inert-lt (q ._≅_.to) $ is-iso→Inert $ Dist.iso→invertible q
Dist-gaunt .has-category .to-path-over p = is-prop→pathp (λ i a b → is-iso→prop a b) Dist.id-iso p
Dist-gaunt .has-strict = hlevel 2

Dist-cat : is-category Dist
Dist-cat = Dist-gaunt .has-category

zero-is-initial : is-initial Dist 0
zero-is-initial _ .centre .map ()
zero-is-initial _ .centre .ascending ()
zero-is-initial _ .paths _ = ext λ ()

zero-is-terminal : is-terminal Dist 0
zero-is-terminal n .centre .map _ = nothing
zero-is-terminal n .centre .ascending _ _ _ = n≲n
zero-is-terminal n .paths x = ext λ y → sym $ refute-just (λ ()) (x · y)

zero-is-zero : is-zero Dist 0
zero-is-zero .is-zero.has-is-initial = zero-is-initial
zero-is-zero .is-zero.has-is-terminal = zero-is-terminal

zero-dist : Zero Dist
zero-dist = record { ∅ = 0 ; has-is-zero = zero-is-zero }
open Zero zero-dist

cast-id : ∀ {n m} → n ≡ m → ⟨ n ⟩→⟨ m ⟩
cast-id p .map (fin k ⦃ q ⦄) = just $ fin k ⦃ ≤-trans q (≤-refl' p) ⦄
cast-id p .ascending j k lt = j≲j lt

dist-peel : ⟨ suc n ⟩→⟨ m ⟩ → ⟨ n ⟩→⟨ m ⟩
dist-peel f .map = f .map ⊙ fsuc
dist-peel f .ascending j k = f .ascending (fsuc j) (fsuc k) ⊙ s≤s

cons-nothing : ⟨ n ⟩→⟨ m ⟩ → ⟨ suc n ⟩→⟨ m ⟩
cons-nothing f .map j with fin-view j
... | zero = nothing
... | suc i = f · i
cons-nothing f .ascending j k lt with fin-view j | fin-view k
... | zero | x = n≲x
... | suc j | suc k = f .ascending j k $ ≤-peel lt

cons-id : ⟨ n ⟩→⟨ m ⟩ → ⟨ suc n ⟩→⟨ suc m ⟩
cons-id f .map j with fin-view j
... | zero = just fzero
... | suc i = fsuc <$> f · i
cons-id f .ascending j k lt with fin-view j | fin-view k
... | zero | x = 0≲x
... | suc j | suc k with f · j | f · k | f .ascending j k (≤-peel lt)
... | nothing | x      | _      = n≲x
... | just j | nothing | _      = x≲n
... | just j | just k  | j≲j lt = j≲j $ s≤s lt

count-defined : (f : ⟨ n ⟩→⟨ m ⟩) → Nat
count-defined {n = zero} _ = 0
count-defined {n = suc n} {m} f =
  ifᵈ holds? (is-just $ f · 0) then
    suc rec
  else
    rec
  where rec = count-defined $ dist-peel f

inj-defined : (f : ⟨ n ⟩→⟨ m ⟩) → ⟨ n ⟩→⟨ count-defined f ⟩
inj-defined {zero} {m} f = ¡
inj-defined {suc n} {m} f with f · 0
... | nothing = cons-nothing $ inj-defined $ dist-peel f
... | just x = cons-id $ inj-defined $ dist-peel f

cons-nothing-inert : (f : ⟨ n ⟩→⟨ m ⟩) → is-inert f → is-inert $ cons-nothing f
cons-nothing-inert {n} f f-inert j .centre .fst = fsuc $ f-inert j .centre .fst
cons-nothing-inert {n} f f-inert j .centre .snd = f-inert j .centre .snd
cons-nothing-inert {n} f f-inert j .paths (x , p) = Σ-prop-path! pp where
  pp : (fsuc $ f-inert j .centre .fst) ≡ x
  pp with fin-view x
  ... | zero = absurd $ᵢ nothing≠just p
  ... | suc i = ap (fsuc ⊙ fst) $ f-inert j .paths $ i , p

peel-fsuc-maybe : (f : Fin n → (Maybe $ Fin m)) → ∀ j k → (fsuc <$> f j) ≡ just (fsuc k) → f j ≡ just k
peel-fsuc-maybe f j k p with f · j
... | nothing = absurd $ᵢ nothing≠just p
... | just x  = ap just $ fsuc-inj $ just-inj p

cons-id-inert : (f : ⟨ n ⟩→⟨ m ⟩) → is-inert f → is-inert $ cons-id f
cons-id-inert f f-inert j .centre .fst with fin-view j
... | zero = fzero
... | suc j = fsuc $ f-inert j .centre .fst
cons-id-inert f f-inert j .centre .snd with fin-view j
... | zero = refl
... | suc j = ap (fsuc <$>_) $ f-inert j .centre .snd
cons-id-inert f f-inert j .paths (x , p) = Σ-prop-path! pp where
  pp : (cons-id-inert f f-inert j .centre .fst) ≡ x
  pp with fin-view j | fin-view x
  pp | zero | zero = refl
  pp | zero | suc k with f · k
  pp | zero | suc k | nothing = absurd $ᵢ nothing≠just p
  pp | zero | suc k | just x = absurd $ᵢ fzero≠fsuc $ sym $ just-inj p
  pp | suc j | zero = absurd $ᵢ fzero≠fsuc $ just-inj p
  pp | suc j | suc k = ap (fsuc ⊙ fst) $ f-inert j .paths $ k , peel-fsuc-maybe (f .map) k j p

inj-inert : (f : ⟨ n ⟩→⟨ m ⟩) → is-inert $ inj-defined f
inj-inert {suc n} {m} f with f · 0
... | nothing = cons-nothing-inert (inj-defined $ dist-peel f) $ inj-inert $ dist-peel f
... | just x = cons-id-inert (inj-defined $ dist-peel f) $ inj-inert $ dist-peel f

inj-inv : (f : ⟨ n ⟩→⟨ m ⟩) → Fin (count-defined f) → Fin n
inj-inv f = inert-inv {f =  inj-defined f} $  inj-inert f

proj-defined : (f : ⟨ n ⟩→⟨ m ⟩) → ⟨ count-defined f ⟩→⟨ m ⟩
proj-defined = {! inj-inv  !}

module factor {n m} (f : ⟨ n ⟩→⟨ m ⟩) where

  CoKer : Type lzero
  CoKer = Σ[ l ∈ Fin n ] is-just (f · l)

  σ : Fin n → Maybe CoKer
  σ l = (l ,_) <$> Dec→Maybe

  -- likewise we can map through f to `Fin m`. This bit must be active
  π : CoKer → Maybe (Fin m)
  π = f .map ⊙ fst

  σ-then-π-is-f : ∀ n → (σ n >>= π) ≡ᵢ f · n
  σ-then-π-is-f j = {! !}

  -- not sure why Listing-prop isn't a class otherwise this is auto
  listing : Listing CoKer
  listing = Listing-Σ ⦃ auto ⦄ ⦃ Listing-prop ⦄
  module listing = Listing listing


  mid : Nat
  mid = listing.card

  left : ⟨ n ⟩→⟨ mid ⟩
  left = {! !}

  right : ⟨ mid ⟩→⟨ m ⟩
  right = {! !}


  left∈L : left ∈ Inert

  left∈R : right ∈ Active

open is-ofs
inert-active-is-ofs : is-ofs Dist Inert Active
inert-active-is-ofs .factor f = record {factor f }
inert-active-is-ofs .is-iso→in-L f = is-iso→Inert
inert-active-is-ofs .L-is-stable f g if ig = is-inert-∘ {f = f} {g} if ig
inert-active-is-ofs .is-iso→in-R f = is-iso→Active
inert-active-is-ofs .R-is-stable f g af ag j with g · j | ag j
inert-active-is-ofs .R-is-stable f g af ag j | just k | _ = af k
inert-active-is-ofs .L⊥R f fi g ga u v sq = goal where
  goal : is-contr (Lifting Dist f g u v)
  goal .centre .fst = {! !}
  goal .centre .snd = {! !}
```
