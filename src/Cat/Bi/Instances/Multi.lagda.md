<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Functor.Closed
open import Cat.Displayed.Functor
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Displayed.Multi.Base
open import Cat.Bi.Base
open import Cat.Prelude

open import 1Lab.Underlying

open import Cat.Bi.Instances.Displayed

import Cat.Displayed.Reasoning as Disp
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Instances.Multi (o ℓ : Level) where
```

<!--
```agda
private variable
  o' ℓ' o'' ℓ'' : Level
```
-->


```agda
module _ where
  open Precategory
  open MultiFunctor
  open Multicat hiding (Ob)
  MultiFunctors : Multicat o' ℓ' → Multicat o'' ℓ'' → Precategory _ _
  MultiFunctors E F .Ob  = MultiFunctor E F
  MultiFunctors E F .Hom G H = G .U =>↓ H .U
  MultiFunctors E F .Hom-set _ _ = hlevel 2
  MultiFunctors E F .id  = idnt↓
  MultiFunctors E F ._∘_ = _∘nt↓_
  MultiFunctors E F .idr f = ext λ x → Cr.idr (Fibre (F .disp) _) _
  MultiFunctors E F .idl f = ext λ x → Cr.idl (Fibre (F .disp) _) _
  MultiFunctors E F .assoc f g h = ext λ x → Cr.assoc (Fibre (F .disp) _) _ _ _
```

<!--
```agda
module _  where
  open Prebicategory

  private
    Mf : Multicat o' ℓ' → Multicat o'' ℓ'' → Precategory _ _
    Mf = MultiFunctors

  open MultiFunctor
  open make-natural-iso
  open Functor
  open _=>↓_
```
-->

```agda

  ∘M-functor' : ∀ {M N S : Multicat o ℓ} → Functor (Mf N S ×ᶜ Mf M N) (Mf M S)
  ∘M-functor' .F₀ (G , F) = G ∘M F
  ∘M-functor' .F₁ (f , g) = f ◆↓ g
  ∘M-functor' .F-id {F , G} = ∘V-functor' _ _ _ .F-id {F .U , G .U}
  ∘M-functor' .F-∘ (α , β) (δ , γ) = ∘V-functor' _ _ _ .F-∘ (α , β) (δ , γ)

  ∘M-functor : ∀ {M N S : Multicat o ℓ} → Bifunctor (Mf N S) (Mf M N) (Mf M S)
  ∘M-functor = Curry ∘M-functor'

```

<!--
```agda
  private
    assoc : Associator-for Mf ∘M-functor
    assoc {C = C} {D} = to-natural-iso ni where
      module D = Multicat D
      module C = Multicat C
      module D' {x} = Cr (Fibre D.disp x)
      module C' {x} = Cr (Fibre C.disp x)

      ni : make-natural-iso {D = Mf _ _} _ _
      ni .eta _ = record { η' = λ x' → D.id' ; is-natural' = λ x y f → D.to-pathp[] D.id-comm[] }
      ni .inv _ = record { η' = λ x' → D.id' ; is-natural' = λ x y f → D.to-pathp[] D.id-comm[] }
      ni .eta∘inv _ = ext λ _ → D'.idl _
      ni .inv∘eta _ = ext λ _ → D'.idl _
      ni .natural x y f = ext λ _ →
          D'.pullr (D'.cancelr (D'.idr _) ∙ ap (x .fst .F₁') (ap₂ C'._∘_ (C'.eliml (y .snd .fst .F-id')) (C'.elimr refl)))
        ∙ sym (D'.eliml refl
          ∙ D'.pullr (D'.pullr (ap₂ D'._∘_ (D'.elimr refl) (D'.elimr refl)) ∙ ap₂ D'._∘_ refl (sym $ Vertical-functor.Fibre-map (x .fst .U) _ .Functor.F-∘ _ _))
          ∙ D'.pulll (D'.eliml (ap (y .fst .F₁') (y .snd .fst .F-id') ∙ y .fst .F-id') ∙ D'.eliml (y .fst .F-id'))
          ∙ ap₂ D'._∘_ (D'.introl (y .fst .F-id')) refl)
```
-->


```agda
  open Multicat hiding (Ob)
  Multicats : Prebicategory (lsuc (o ⊔ ℓ)) (o ⊔ ℓ) (o ⊔ ℓ)
  Multicats .Ob = Multicat o ℓ
  Multicats .Hom = MultiFunctors
  Multicats .id = IdM _
  Multicats .compose = ∘M-functor
  Multicats .unitor-l {B = B} = to-natural-iso ni where
    module B = Disp (B .disp)
    module B' {x} = Cr (Fibre (B .disp) x)

    ni : make-natural-iso {D = Mf _ _} _ _
    ni .eta _ = record { η' = λ x' → B.id' ; is-natural' = λ x y f → B.to-pathp[] B.id-comm[] }
    ni .inv _ = record { η' = λ x' → B.id' ; is-natural' = λ x y f → B.to-pathp[] B.id-comm[] }
    ni .eta∘inv _ = ext λ _ → B'.idl _
    ni .inv∘eta _ = ext λ _ → B'.idl _
    ni .natural x y f = ext λ _ → B'.elimr refl ∙ B'.id-comm
  Multicats .unitor-r {B = B} = to-natural-iso ni where
    module B = Disp (B .disp)
    module B' {x} = Cr (Fibre (B .disp) x)

    ni : make-natural-iso {D = Mf _ _} _ _
    ni .eta _ = record { η' = λ x' → B.id' ; is-natural' = λ x y f → B.to-pathp[] B.id-comm[] }
    ni .inv _ = record { η' = λ x' → B.id' ; is-natural' = λ x y f → B.to-pathp[] B.id-comm[] }
    ni .eta∘inv _ = ext λ _ → B'.idl _
    ni .inv∘eta _ = ext λ _ → B'.idl _
    ni .natural x y f = ext λ _ → B'.elimr refl ∙ ap₂ B'._∘_ (y .F-id') refl
  Multicats .associator = assoc
  Multicats .triangle {C = C} f g = ext λ _ → Cr.idr (Fibre (C .disp) _) _
  Multicats .pentagon {E = E} f g h i = Disp[] _ o ℓ .pentagon (f .U) (g .U) (h .U) (i .U)
```
