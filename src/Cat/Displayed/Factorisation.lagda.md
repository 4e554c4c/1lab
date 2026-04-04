<!--
```agda
open import Cat.Morphism.Factorisation.Orthogonal
open import Cat.Morphism.Factorisation
open import Cat.Morphism.Orthogonal
open import Cat.Displayed.Total.Op
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Morphism.Class
open import Cat.Morphism.Lifts
open import Cat.Prelude

import Cat.Displayed.Morphism.Duality
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Factorisation
  {o ℓ ℓl ℓr o' ℓ'} {ℬ : Precategory o ℓ} (L :  Arrows ℬ ℓl) (R :  Arrows ℬ ℓr) (ℰ : Displayed ℬ o' ℓ') where
```

<!--
```agda
open Cat.Displayed.Morphism.Duality ℰ
open Cat.Displayed.Morphism ℰ
open Cat.Reasoning ℬ
open module ℰ = DR ℰ
open import Cat.Displayed.Cartesian ℰ
```
-->

# Displayed categories and factorisation systems

Suppose that we have two classes of morphisms $(L, R)$ on $B$. What are
the sufficient conditions for a category $E$ displayed over $B$ to have
a factorisation system $(\overline L, \overline R)$ over $(L, R)$?

```agda

module lifts→ofs-over (ofs : is-ofs ℬ L R) (lifts-R : ∀ {x y} (f : Hom x y) → (f ∈ R) → has-cartesian-lifts f) where

  private
    module ofs = is-ofs ofs
  -- L' is the fibre over L
  L' : Arrows (∫ ℰ) ℓl
  L' .arrows (∫hom f _) = f ∈ L
  L' .is-tr = hlevel 1

  -- but R' is all cartesian lifts of morphisms in R
  R' : Arrows (∫ ℰ) (o ⊔ ℓ ⊔ ℓr ⊔ o' ⊔ ℓ')
  R' .arrows (∫hom f f') = f ∈ R × is-cartesian f f'
  R' .is-tr = hlevel 1

  module _ {x^ y^} (f^ : ∫Hom ℰ x^ y^) where
    open ∫Hom f^ renaming (fst to f; snd to f')
    open Σ x^ renaming (fst to x; snd to x')
    open Σ y^ renaming (fst to y; snd to y')

    module fact = Factorisation (ofs.factor f)

    clift = lifts-R fact.right fact.right∈R y'
    open module clift = Cartesian-lift clift using () renaming (x' to mid')

    -- now f' : Hom[ f ] x' y'
    -- but f = right ∘ left, so ff = transp _ f : Hom[ right ∘ left ] x' y'
    -- and thus we can lift it to (lift ff) : Hom [ left ] x' m'

    --f'' : Hom[ fact.right ∘ fact.left ] x' y'
    --f'' = hom[ fact.factors ] f'

    open Factorisation
    factor' : Factorisation (∫ ℰ) L' R' f^
    factor' .mid = fact.mid , mid'
    factor' .left =
      ∫hom fact.left $ clift.universal' (sym fact.factors) f'
    factor' .right = ∫hom fact.right clift.lifting
    factor' .left∈L = fact.left∈L
    factor' .right∈R = fact.right∈R , clift.cartesian
    factor' .factors = ∫Hom-path ℰ fact.factors $ symP $ clift.commutesp (sym fact.factors) f'


  open is-ofs
  open Factorisation
  open Cartesian-lift
  open is-cartesian
  main-theoremm : is-ofs (∫ ℰ) L' R'
  main-theoremm .factor f = factor' f
  main-theoremm .is-iso→in-L (∫hom f _) x = ofs.is-iso→in-L f (total-invertible→invertible ℰ x)
  main-theoremm .L-is-stable f g p q = ofs.L-is-stable _ _ p q
  main-theoremm .is-iso→in-R f x .fst = ofs.is-iso→in-R _ (total-invertible→invertible ℰ x)
  main-theoremm .is-iso→in-R f x .snd = invertible→cartesian _ (total-invertible→invertible[] ℰ x)
  main-theoremm .R-is-stable f g (p , c) (q , c') .fst = ofs.R-is-stable _ _ p q
  main-theoremm .R-is-stable f g (p , c) (q , c') .snd = cartesian-∘ c c'
  main-theoremm .L⊥R f^@(∫hom f f') p g^@(∫hom g g') (q , c) u^@(∫hom u u') v^@(∫hom v v') comm
    using (contr (l , pt , pb) ps) ← (ofs.L⊥R f p g q u v (ap ∫Hom.fst comm)) = goal
    where
      open ∫Hom
      module c = is-cartesian c

      l' = c.universal' pb v'

      goal : is-contr (Lifting (∫ ℰ) f^ g^ u^ v^)
      goal .centre .fst = ∫hom l l'
      goal .centre .snd .snd = ∫Hom-path _ pb $ c.commutesp pb v'
      goal .centre .snd .fst = ∫Hom-path _ pt $ cartesian→weak-monic c _ _ pt $ cast[] $
        g' ∘' l' ∘' f' ≡[]⟨ pulll[] pb $ c.commutesp pb v' ⟩
        v' ∘' f'       ≡[]⟨ ap snd comm ⟩
        g' ∘' u'       ∎
      goal .paths (∫hom m m' , (pt' , pb')) = Σ-prop-path!
        $ ∫Hom-path _ (ap fst $ ps $ m , ap fst pt' , ap fst pb')
        $ symP $ c.uniquep (ap fst pb') _ _ m' $ ap snd pb'
```

