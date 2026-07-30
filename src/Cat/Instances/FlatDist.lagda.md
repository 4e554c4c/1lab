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
open import Data.Sum.Base
open import Data.Nat -- using (H-Level-Nat; s≤s; 0≤x ; ≤-trans)
open import Data.Dec.Base
open import Data.Fin renaming (_≤_ to _≤f_; _<_ to _<f_)
open import Data.Fin.Monotone

open import Data.Set.Coequaliser
open import Data.Bool.Base
open import Data.Maybe.Properties
open import Data.Fin.Closure
open import Cat.Functor.Naturality
open import Cat.Monoidal.Braided
open import Data.Fin.Properties
open import Data.Sum
open import Data.Nat.Properties
open import Cat.Monoidal.Base
open import Cat.Functor.Bifunctor

import Cat.Reasoning
import Cat.Morphism

open import Meta.Idiom

open Functor
```
-->

```agda
module Cat.Instances.FlatDist where

private variable
  n m l n' m' : Nat

record ⟨_⟩→⟨_⟩ (n m : Nat) : Type where
  constructor sasc
  field
    map       : (Fin $ suc n) → (Fin $ suc m)
    point     : map 0 ≡ᵢ 0
    ascending : (x y : Fin $ suc n) → (map x ≠ᵢ 0) → (map y ≠ᵢ 0) → x ≤f y → map x ≤f map y

unquoteDecl H-Level-⟨⟩→⟨⟩ = declare-record-hlevel 2 H-Level-⟨⟩→⟨⟩ (quote ⟨_⟩→⟨_⟩)

open ⟨_⟩→⟨_⟩

⟨⟩→⟨⟩-path
  : ∀ {n m : Nat} {f g : ⟨ n ⟩→⟨ m ⟩}
  → (∀ x → f .map x ≡ g .map x)
  → f ≡ g
⟨⟩→⟨⟩-path p i .map x = p x i
⟨⟩→⟨⟩-path {m = m} {f = f} {g} p i .point =
  is-prop→pathp (λ j → hlevel {T = p 0 j ≡ᵢ 0} 1) (f .point) (g .point) i  
⟨⟩→⟨⟩-path {f = f} {g} p i .ascending x y a b w =
  is-prop→pathp (λ j → ≤-is-prop {p x j .lower} {p y j .lower})
    (f .ascending x y fx fy w) (g .ascending x y gx gy w) i where
   --fx : f .map x ≠ᵢ fin 0
   --fy : f .map y ≠ᵢ fin 0
   --gx : g .map x ≠ᵢ fin 0
   --gy : g .map y ≠ᵢ fin 0
   fx =  subst (_≠ᵢ _) (λ j →  p x (i ∧ ~ j)) a
   fy =  subst (_≠ᵢ _) (λ j →  p y (i ∧ ~ j)) b
   gx =  subst (_≠ᵢ _) (λ j →  p x (i ∨ j)) a
   gy =  subst (_≠ᵢ _) (λ j →  p y (i ∨ j)) b

instance
  Funlike-⟨⟩→⟨⟩ : ∀ {n m} → Funlike ⟨ n ⟩→⟨ m ⟩ (Fin $ suc n) λ _ → (Fin $ suc m)
  Funlike-⟨⟩→⟨⟩ = record { _·_ = ⟨_⟩→⟨_⟩.map }

  Extensional-⟨⟩→⟨⟩ : ∀ {n m} → Extensional ⟨ n ⟩→⟨ m ⟩ lzero
  Extensional-⟨⟩→⟨⟩ {n} .Pathᵉ   f g = ∀ (j : Fin $ suc n) → (f · j) ≡ (g · j)
  Extensional-⟨⟩→⟨⟩ .reflᵉ _ j = refl
  Extensional-⟨⟩→⟨⟩ .idsᵉ .to-path = ⟨⟩→⟨⟩-path
  Extensional-⟨⟩→⟨⟩ .idsᵉ .to-path-over p = is-prop→pathp (λ i → hlevel 1) (λ j → refl) p

dist-∘ : ∀{n m k} (f : ⟨ m ⟩→⟨ k ⟩) (g : ⟨ n ⟩→⟨ m ⟩) → ⟨ n ⟩→⟨ k ⟩
dist-∘ f g .map = f .map ⊙ g .map
dist-∘ f g .point = apᵢ (f .map) (g .point)  ∙ᵢ f .point
dist-∘ f g .ascending x y a b p =  f .ascending _ _ a b $  g .ascending _ _
  (λ n → a $ apᵢ (f .map) n ∙ᵢ f .point ) (λ n → b $ apᵢ (f .map) n ∙ᵢ f .point) p 

dist-id : ∀ {n} → ⟨ n ⟩→⟨ n ⟩
dist-id .map x = x
dist-id .point =  reflᵢ
dist-id .ascending _ _ _ _ le = le

all-one : ∀ {n} → ⟨ n ⟩→⟨ 1 ⟩
all-one .map fzero = 0
all-one .map (fin (suc _)) = 1
all-one .point = reflᵢ
all-one .ascending x y _ _ lt with fin-view x | fin-view y
... | zero | zero = _
... | zero | suc i = _
... | suc i | suc i₁ = _

is-inert : ∀ {n m} → ⟨ n ⟩→⟨ m ⟩ → Type
is-inert (sasc f _ _) = ∀ x → is-contr (fibreᵢ f $ fsuc x)

ρ[_] : ∀ {n} → Fin n → ⟨ n ⟩→⟨ 1 ⟩
ρ[ k ] .map x = ifᵈ (x ≡ᵢ? fsuc k) then 1 else 0
ρ[ k ] .point =  reflᵢ
ρ[ k ] .ascending x y p q le with (x ≡ᵢ? fsuc k) | (y ≡ᵢ? fsuc k)
... | no ¬a | q = 0≤x
... | yes a | yes b = _
... | yes a | no ¬b = absurd $ q reflᵢ

ρ-inert : ∀ {n k} → is-inert {n} ρ[ k ]
ρ-inert {n} {k} d .centre .fst = fsuc k
ρ-inert {n} {k} d .centre .snd rewrite ≡?-yes (fsuc k) with fin-view d
... | zero = reflᵢ
ρ-inert {n} {k} d .paths (k' ,  p) =  Σ-prop-path! (sym pf) where
  pf : k' ≡ fsuc k
  pf with (k' ≡ᵢ? fsuc k)
  ... | yes q =  Id≃path.to q

fpred' : ∀ {n} → (f : Fin (suc n)) → (f ≠ᵢ 0) → Fin n
fpred' n p with fin-view n
... | zero =  absurd $ p reflᵢ
... | suc i = i

inert-inv : ∀ {n m} → {f : ⟨ n ⟩→⟨ m ⟩} → is-inert f → (Fin m → Fin n)
inert-inv {n}{m}{f} inert k = fpred' (inert k .centre .fst) λ p →
  fsuc≠fzero $ Id≃path.to $ symᵢ (inert k .centre .snd) ∙ᵢ apᵢ (f .map) p ∙ᵢ f .point  

is-active : ∀ {n m} → ⟨ n ⟩→⟨ m ⟩ → Type
is-active {n} {m} f = ∀ (j : Fin n) → (f · fsuc j) ≠ᵢ 0

lift-active : (f : ⟨ n ⟩→⟨ m ⟩) → (is-active f) → Fin n → Fin m
lift-active f active k = fpred' (f · fsuc k) (active k)

FlatDist : Precategory lzero lzero
FlatDist .Precategory.Ob = Nat
FlatDist .Precategory.Hom n m = ⟨ n ⟩→⟨ m ⟩
FlatDist .Precategory.Hom-set _ _ = hlevel 2
FlatDist .Precategory._∘_ = dist-∘
FlatDist .Precategory.id = dist-id
FlatDist .Precategory.idr f = refl
FlatDist .Precategory.idl f = trivial!
FlatDist .Precategory.assoc f g h = trivial!


module sum {n} {m} = Equiv (Finite-coproduct {n} {m})

open Precategory FlatDist
open make-natural-iso


_f+_ : Fin n → Fin m → Fin (n + m)
fin j ⦃ lt ⦄ f+ fin k ⦃ lt' ⦄ = fin (j + k) ⦃ +-preserves-< _ _ _ _ lt lt' ⦄

module _ where
  open Make-bifunctor
  open ⟨_⟩→⟨_⟩
  open F+-monotonic
  open From-lt-cases
  bb : Make-bifunctor {C = FlatDist} {D = FlatDist} {E = FlatDist}
  bb .F₀ n m = n + m
  bb .lmap {n} {m} {l} f .map (fin k ⦃ lt ⦄) with holds? (k < suc n)
  ... | yes a =  weaken' (s≤s $ +-≤l _ _) (f · fin k ⦃ a ⦄)
  ... | no ¬a =  fin m ⦃ Leq-refl ⦄ f+  fin (k - (suc n)) ⦃ monus-<-swapl lt (≤-peel $ <-from-not-≤ _ _ ¬a) ⦄
  bb .lmap {n} {m} {l} f .point = fin-apᵢ (apᵢ lower $ f .point)
  bb .lmap {n} {m} {l} f .ascending (fin j ⦃ l1 ⦄) (fin k ⦃ l2 ⦄) a b lt with (holds? $ j < suc n) | (holds? $ k < suc n) 
  ... | yes x | yes y =  f .ascending _ _ (λ ¬a →  a $ fin-apᵢ $ apᵢ lower ¬a) (λ ¬b →  b $ fin-apᵢ $ apᵢ lower ¬b)  lt
  ... | yes x | no ¬y = {!!}
  ... | no ¬x | yes y = {!!}
  ... | no ¬x | no ¬y =  +-preserves-≤l _ _ m  $ monus-preserves-≤l (suc n) lt  
  bb .rmap {n} {m} {l} g .map (fin k ⦃ lt ⦄) with holds? (k < suc l)
  ... | yes a =  fin k ⦃ a ≤∙ ( s≤s $ +-≤l _ _) ⦄
  ... | no ¬a =   fin l ⦃ Leq-refl ⦄  f+  fpred' (g .map (fin (k - (suc l)) ⦃ {! monus-≤-swapl !} ⦄)) {! g .:qa!}  
  --bb .rmap {n} {m} {l} g .map y =  [ pure ⊙ sum.to ⊙ inl , sum.to ⊙ inr <∙> g .map ] $ sum.from y
  --bb .rmap {n} {m} {l} g .ascending j k lt with from-lt-cases {l} {n}  j k lt
  --bb .rmap {n} {m} {l} g .ascending j k lt | ll j' k' w w' lt' rewrite w rewrite w' = j≲j $ to-inl {m = l} j' k' lt'
  --bb .rmap {n} {m} {l} g .ascending j k lt | lr j' k' w w' rewrite w rewrite w' with g · k'
  --bb .rmap {n} {m} {l} g .ascending j k lt | lr j' k' w w' | nothing = j≲n
  --bb .rmap {n} {m} {l} g .ascending j k lt | lr j' k' w w' | just x = j≲j $ <-weaken $ inl<inr {n = l} {m = m} j' x
  --bb .rmap {n} {m} {l} g .ascending j k lt | rr j' k' w w' lt' rewrite w rewrite w' =  Map-≲ (λ {x} {y} lt  → to-inr {n = l} x y lt) $ g .ascending _ _ lt'
  --bb .lmap-id {n} {m} = ext λ k → p k where
  -- p : ∀ k → [ sum.to ⊙ inl <∙> id .map , just ⊙ sum.to ⊙ inr ] (sum.from {n} {m} k) ≡ just k
  -- p k with sum.from {n} {m} k in w
  -- ... | inl x = ap just $ sum.adjunctr $ sym $ Id≃path.to w
  -- ... | inr x = ap just $ sum.adjunctr $ sym $ Id≃path.to w
```
