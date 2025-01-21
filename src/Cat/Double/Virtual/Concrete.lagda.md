<!--
```agda
open import Cat.Prelude hiding (∣_∣)
```
-->

```agda
module Cat.Double.Virtual.Concrete (ℓo ℓt ℓl ℓ□ : Level)  where
```

# Double categories


```agda
--open import Data.Fin.Product using (Πᶠ)
open import Cat.Instances.Shape.Cospan using (·←·→·)
open import Cat.Functor.Base using (Cat[_,_])
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Universe
open import 1Lab.Reflection
--open import 1Lab.Type

level-of-vdbl : Level
level-of-vdbl = (lsuc (ℓo ⊔ ℓt ⊔ ℓl ⊔ ℓ□))

module multi {o a : Level} (Ob : Type o) (Arr : Ob → Ob → Type a) where
  data MultiArr : Ob → Ob → Type (o ⊔ a) where
    [] : {X : Ob} → MultiArr X X
    cons : ∀ {X : Ob} {Y : Ob} {Z : Ob} → Arr X Y → MultiArr Y Z → MultiArr X Z
  -- it often helps with unification to give the middle object explicitly
  syntax cons {Y = Y} h M = h :⟨ Y ⟩: M

  mconcat : ∀ {a b c} → MultiArr a b → MultiArr b c → MultiArr a c
  mconcat [] m = m
  mconcat (cons f n) m = cons f (mconcat n m)

record VirtualDoubleCategoryData : Type level-of-vdbl where
  no-eta-equality
  field
    TightCat  : Precategory ℓo ℓt
  open module TightCat = Precategory TightCat renaming (Hom to Tight; Hom-set to Tight-set; idr to tidr; idl to tidl; assoc to tassoc) public
  field
    Loose : Ob → Ob → Type ℓl
    -- is this necessary?
    Loose-set : (x y : Ob) → is-set (Loose x y)
  open multi Ob Loose public
  field
    Cell : ∀ {X X' Y Y'} (f : Tight X X') (m : MultiArr X Y) (q : Loose X' Y') (g : Tight Y Y')  → Type ℓ□

  module MCell = multi (Σ[ X ∈ Ob ] Σ[ X' ∈ Ob ] Tight X X') (λ (X , X' , f) (Y , Y' , g) → Σ[ m ∈ MultiArr X Y ] Σ[ q ∈  Loose X' Y' ] Cell f m q g)
  open MCell using () renaming (MultiArr to MultiCell; cons to cellcons; [] to c[]) public

  top : ∀ {X X' f Y Y' g} → MultiCell (X , X' , f) (Y , Y' , g) → MultiArr X Y
  top c[] = []
  top (cellcons (m , _ , _) cs) = mconcat m (top cs)

  bot : ∀ {X X' f Y Y' g} → MultiCell (X , X' , f) (Y , Y' , g) → MultiArr X' Y'
  bot c[] = []
  bot (cellcons (_ , f , _) cs) = cons f (bot cs)

record VirtualDoubleCategoryStructure (d : VirtualDoubleCategoryData) : Type level-of-vdbl where
  open VirtualDoubleCategoryData d

  field
    vcomp : ∀ {X X' X'' f Y Y' Y'' g q} {f' : Tight X' X''} {g' : Tight Y' Y''} (mc : MultiCell (X , X' , f) (Y , Y' , g)) → Cell f' (bot mc) q g' → Cell (f' ∘ f) (top mc) q (g' ∘ g)

record VirtualDoubleCategory : Type level-of-vdbl where
  no-eta-equality
  field
    Data : VirtualDoubleCategoryData
    Struct : VirtualDoubleCategoryStructure Data
  open VirtualDoubleCategoryData Data public
  open VirtualDoubleCategoryStructure Struct public

{-
module _ (ℓo ℓt ℓl ℓ□ : Level) (d : VirtualDoubleCategoryArrows ℓo ℓt ℓl) where
  -- now we need a type to describe the 'top' of a cell
  open VirtualDoubleCategoryArrows d
-}


```
