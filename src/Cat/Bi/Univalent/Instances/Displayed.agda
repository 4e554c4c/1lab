
open import Cat.Prelude

open import Cat.Functor.Base
open import Cat.Functor.Naturality
open import Cat.Functor.Compose renaming (_◆_ to _◇_)

open import Cat.Bi.Base
open import Cat.Bi.Univalent
open import Cat.Functor.Univalence
open import Cat.Bi.Diagram.Adjunction
open import Cat.Bi.AdjointEquiv
open import Cat.Functor.Adjoint.Unique
open import Cat.Functor.Equivalence.Path
open import Cat.Bi.Instances.Displayed

import Cat.Functor.Bifunctor as Bi
import Cat.Reasoning as Cr
import Cat.Univalent
import Cat.Functor.Equivalence as FunEquiv
import Cat.Functor.Reasoning as Fr
import Cat.Natural.Reasoning

open import Cat.Displayed.Functor.Univalence
open import Cat.Displayed.Functor
open import Cat.Displayed.Path
open import Cat.Functor.Bifunctor
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Displayed.Univalence
open import Cat.Displayed.Univalence.Reasoning
import Cat.Displayed.Reasoning as Disp
import Cat.Reasoning as Cat
module Cat.Bi.Univalent.Instances.Displayed (o ℓ : Level)  (B : Precategory o ℓ) (o' ℓ' : Level) where
open Vertical-functor
open make-natural-iso
open Functor
open _=>↓_
open Make-bifunctor


module Disp[] = Prebicategory (Disp[] B o' ℓ')
private module _ where
  open Functor
  {-
  assoc : Associator-for {O = Σ[ C ∈ Precategory o ℓ ] is-category C} (λ C D → Cat[ C .fst , D .fst ]) F∘-functor
  assoc {D = (D , _)} = to-natural-iso ni where
    module D = Cr D using (id ; idl ; id-comm-sym ; idr ; pushr ; introl)
    ni : make-natural-iso {D = Cat[ _ , _ ]} _ _
    ni .make-natural-iso.eta x = NT (λ _ → D.id) λ _ _ _ → D.id-comm-sym
    ni .make-natural-iso.inv x = NT (λ _ → D.id) λ _ _ _ → D.id-comm-sym
    ni .make-natural-iso.eta∘inv x = ext λ _ → D.idl _
    ni .make-natural-iso.inv∘eta x = ext λ _ → D.idl _
    ni .make-natural-iso.natural x y f = ext λ _ →
      D.idr _ ∙∙ D.pushr (x .fst .F-∘ _ _) ∙∙ D.introl refl
      -}
  assoc : Associator-for {O = Σ[ B ∈ Displayed B o' ℓ' ] is-category-displayed B} (λ E F → Cat↓[ E .fst , F .fst ]) (∘V-functor B o' ℓ')
  assoc {C = (C , _)} {D = (D , _)} = to-natural-iso ni where
    module D = Disp D
    module D' {x} = Cat (Fibre D x)
    module C' {x} = Cat (Fibre C x)

    ni : make-natural-iso {D = Cat↓[ _ , _ ]} _ _
    ni .eta _ = record { η' = λ x' → D.id' ; is-natural' = λ x y f → D.to-pathp[] D.id-comm[] }
    ni .inv _ = record { η' = λ x' → D.id' ; is-natural' = λ x y f → D.to-pathp[] D.id-comm[] }
    ni .eta∘inv _ = ext λ _ → D'.idl _
    ni .inv∘eta _ = ext λ _ → D'.idl _
    ni .natural x y f = ext λ _ →
        D'.pullr (D'.cancelr (D'.idr _) ∙ ap (x .fst .F₁') (ap₂ C'._∘_ (C'.eliml (y .snd .fst .F-id')) (C'.elimr refl)))
      ∙ sym (D'.eliml refl
        ∙ D'.pullr (D'.pullr (ap₂ D'._∘_ (D'.elimr refl) (D'.elimr refl)) ∙ ap₂ D'._∘_ refl (sym (Vertical-functor.Fibre-map (x .fst) _ .Functor.F-∘ _ _)))
        ∙ D'.pulll (D'.eliml (ap (y .fst .F₁') (y .snd .fst .F-id') ∙ y .fst .F-id') ∙ D'.eliml (y .fst .F-id'))
        ∙ ap₂ D'._∘_ (D'.introl (y .fst .F-id')) refl)

module _ where
  open Prebicategory
  UDisp[] : Prebicategory (o ⊔ ℓ ⊔ lsuc o' ⊔ lsuc ℓ') (o ⊔ ℓ ⊔ o' ⊔ ℓ') (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  UDisp[] .Ob = Σ[ E ∈ Displayed B o' ℓ' ] is-category-displayed E
  UDisp[] .Hom (C , _ ) (D , _) = Disp[].Hom C D
  UDisp[] .id = Disp[].id
  UDisp[] .compose = Disp[].compose
  UDisp[] .unitor-l = Disp[].unitor-l
  UDisp[] .unitor-r = Disp[].unitor-r
  UDisp[] .associator = assoc
  UDisp[] .triangle f g = reext! (Disp[].triangle f g)
  UDisp[] .pentagon f g h i = reext! (Disp[].pentagon f g h i)

open is-bicategory
open Cat B
UDisp[]-is-bicat : is-bicategory UDisp[]
UDisp[]-is-bicat .is-local (A , _) (B , univ) = Vertical-functor-is-category A B univ
UDisp[]-is-bicat .is-global .to-path {a = E , E-univ} {F , F-univ} adj = Σ-prop-path! $ Displayed-path To (λ a → is-iso→is-equiv $ p₁ a) p₂ where
  open module adj = adjoint-equivalence adj
  module To = Displayed-functor To
  module From = Displayed-functor From
  module E = Disp E
  module F = Disp F
  open is-iso
  p₁ :  (a : Ob) → is-iso (To.₀')
  p₁ a .from = From.₀'
  p₁ a .linv x = vertical-iso→path E E-univ record where
      to' = η⁻¹ .η' x
      from' = η .η' x
      inverses' = record
        { invl' = E.to-pathp[] $ unit-iso.invr η↓ₚ x
        ; invr' = E.to-pathp[] $ unit-iso.invl η↓ₚ x
        }
  p₁ a .rinv x = vertical-iso→path F F-univ record where
      to' = ε .η' x
      from' = ε⁻¹ .η' x
      inverses' = record
        { invl' = F.to-pathp[] $ counit-iso.invl η↓ₚ x
        ; invr' = F.to-pathp[] $ counit-iso.invr η↓ₚ x
        }

  p₂ : ∀ {a b} {f : Hom a b} {a' : E.Ob[ a ]} {b' : E.Ob[ b ]} → is-equiv (To.₁'  {f = f} {a' = a'} {b' = b'})
  p₂ {a} {b} {f} {a'} {b'} = {! !}
UDisp[]-is-bicat .is-global .to-path-over {a = E , E-univ} {F , F-univ} adj = {! ⊣-path ? ? !} where
  open module adj = adjoint-equivalence adj
  module To = Displayed-functor To
  module From = Displayed-functor From
  module E = Disp E
  module F = Disp F

