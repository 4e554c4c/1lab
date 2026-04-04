<!--
```agda
open import Cat.Morphism.Factorisation
open import Cat.Displayed.Base
open import Cat.Morphism.Class
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.Morphism.Class
  {o ℓ o' ℓ'} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o' ℓ') where
```


<--
```agda
open Displayed ℰ
open Precategory ℬ
```
-->

```agda
record Arrows-over {ℓl} (A : Arrows ℬ ℓl) (κ : Level) : Type (ℓl ⊔ o ⊔ ℓ ⊔ o' ⊔ ℓ' ⊔ lsuc κ) where
  no-eta-equality
  field
    arrows-over : ∀ {x y x' y'} {f : Hom x y} →  f ∈ A → Hom[ f ] x' y' → Type κ
    is-tr  : ∀ {x y x' y'} {f : Hom x y} {f' : Hom[ f ] x' y'} {p : f ∈ A} → is-prop (arrows-over p f')

open Arrows-over public

instance
   Membership-Arrows-over : ∀ {ℓl κ} {x y x' y'} {A : Arrows ℬ ℓl} {f : Hom x y} → Membership (f ∈ A × Hom[ f ] x' y') (Arrows-over A κ) κ
   Membership-Arrows-over = record { _∈_ = λ (p , f') S → Arrows-over.arrows-over S p f' }
```
