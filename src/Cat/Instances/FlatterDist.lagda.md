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

open import Meta.Idiom renaming (map to fmap)

open Functor
```
-->

```agda
module Cat.Instances.FlatterDist where

private variable
  n m l n' m' : Nat

record ⟨_⟩→⟨_⟩ (n m : Nat) : Type where
  constructor sasc
  field
    map       : Nat → Nat
    bound     : ∀ k → (k ≤ n) → (map k ≤ m)
    support   : ∀ k → (k > n) → (map k ≡ᵢ 0)
    point     : map 0 ≡ᵢ 0
    ascending : (x y : Nat) → (map x ≠ᵢ 0) → (map y ≠ᵢ 0) → x ≤ y → map x ≤ map y

  point' : ∀ {k} → k ≡ᵢ 0 → map k ≡ᵢ 0
  point' reflᵢ = point

  support-bounded : ∀ {k} → (map k ≠ᵢ 0) → k ≤ n
  support-bounded ne = ≤-from-not-< _ _ λ gt → ne $ support _ gt 

  ctrp : ∀ {k} → (map k ≠ᵢ 0) → k ≠ᵢ 0
  ctrp = _⊙ point'


unquoteDecl H-Level-⟨⟩→⟨⟩ = declare-record-hlevel 2 H-Level-⟨⟩→⟨⟩ (quote ⟨_⟩→⟨_⟩)

open ⟨_⟩→⟨_⟩

unquoteDecl ⟨⟩→⟨⟩-path' = declare-record-path ⟨⟩→⟨⟩-path' (quote ⟨_⟩→⟨_⟩)

⟨⟩→⟨⟩-path
  : ∀ {n m : Nat} {f g : ⟨ n ⟩→⟨ m ⟩}
  → (∀ x → f .map x ≡ g .map x)
  → f ≡ g
⟨⟩→⟨⟩-path = ⟨⟩→⟨⟩-path' ⊙ funext

instance
  Funlike-⟨⟩→⟨⟩ : ∀ {n m} → Funlike ⟨ n ⟩→⟨ m ⟩ Nat λ _ → Nat
  Funlike-⟨⟩→⟨⟩ = record { _·_ = ⟨_⟩→⟨_⟩.map }

  Extensional-⟨⟩→⟨⟩ : ∀ {n m} → Extensional ⟨ n ⟩→⟨ m ⟩ lzero
  Extensional-⟨⟩→⟨⟩ {n} .Pathᵉ   f g = ∀ j → (f · j) ≡ (g · j)
  Extensional-⟨⟩→⟨⟩ .reflᵉ _ j = refl
  Extensional-⟨⟩→⟨⟩ .idsᵉ .to-path = ⟨⟩→⟨⟩-path
  Extensional-⟨⟩→⟨⟩ .idsᵉ .to-path-over p = is-prop→pathp (λ i → hlevel 1) (λ j → refl) p

dist-∘ : ∀{n m k} (f : ⟨ m ⟩→⟨ k ⟩) (g : ⟨ n ⟩→⟨ m ⟩) → ⟨ n ⟩→⟨ k ⟩
dist-∘ f g .map = f .map ⊙ g .map
dist-∘ f g .point = point' f $ g .point
dist-∘ f g .bound k le = f .bound _ $ g .bound k le
dist-∘ f g .support k gt = point' f $ g .support k gt 
dist-∘ f g .ascending x y a b p =
  f .ascending _ _ a b $
  g .ascending _ _ (ctrp f a) (ctrp f b) p

dist-id : ∀ {n} → ⟨ n ⟩→⟨ n ⟩
dist-id {n} .map x = caseᵈ (x ≤ n) of λ where
  (yes a) → x
  (no ¬a) → 0
dist-id .point = reflᵢ
dist-id {n} .bound x p rewrite decide-yes (holds? $ x ≤ n) p = p
dist-id {n} .support x p rewrite decide-no (holds? $ x ≤ n) (<-≤-asym p)
  = reflᵢ
dist-id {n} .ascending x y a b le = {!!}
--  rewrite decide-yes (holds? $ x ≤ n) (support-bounded dist-id a)
--  rewrite decide-yes (holds? $ y ≤ n) (support-bounded dist-id b)
--  = le 
```
