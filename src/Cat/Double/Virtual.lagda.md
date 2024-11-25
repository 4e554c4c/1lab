<!--
```agda
open import Cat.Prelude hiding (∣_∣)
```
-->

```agda
module Cat.Double.Virtual where
```

# Double categories

```agda

open import Data.Fin.Product using (Πᶠ)
open import Cat.Instances.Shape.Cospan using (·←·→·)
open import Cat.Functor.Base using (Cat[_,_])
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Universe
open import 1Lab.Reflection
open import 1Lab.Type


{-
module multi (o a : Level) (Ob : Type o) (Arr : Ob → Ob → Type a) where
  data MultiArr : Ob → Ob → Type (o ⊔ a) where
    [] : {X : Ob} → MultiArr X X
    consWith : ∀ {X : Ob} (Y : Ob) {Z : Ob} → Arr Y X → MultiArr Y Z → MultiArr Z X

  syntax consWith Y h M = h :⟨ Y ⟩: M


record VirtualDoubleCategory (ℓo ℓt ℓl ℓ□ : Level) : Type (lsuc (ℓo ⊔ ℓt ⊔ ℓl ⊔ ℓ□)) where
  no-eta-equality
  field
    TightCat  : Precategory ℓo ℓt

  open module TightCat = Precategory TightCat renaming (Hom to Tight; Hom-set to Tight-set; idr to tidr; idl to tidl; assoc to tassoc) public

  field
    Loose : Ob → Ob → Type ℓl
    -- is this necessary?
    Loose-set : (x y : Ob) → is-set (Loose x y)

  open multi ℓo ℓl Ob Loose

  field
    Cell : ∀ {X X' Y Y'} (f : Tight X X') (m : MultiArr X Y) (q : Loose X' Y') (g : Tight Y' Y)  → Type ℓ□

    id : ∀ {X Y} (q : Loose X Y) → Cell id (q :⟨ X ⟩: []) q id


module _ (ℓo ℓt ℓl ℓ□ : Level) (d : VirtualDoubleCategoryArrows ℓo ℓt ℓl) where
  -- now we need a type to describe the 'top' of a cell

  open VirtualDoubleCategoryArrows d

-}

```
