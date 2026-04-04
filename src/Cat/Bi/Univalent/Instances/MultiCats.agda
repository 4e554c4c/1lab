
open import Cat.Prelude

open import Cat.Functor.Base
open import Cat.Instances.Dist
open import Cat.Displayed.Multi.Base
open import Cat.Functor.Naturality
open import Cat.Functor.Compose renaming (_◆_ to _◇_)
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base

open import Cat.Bi.Base
open import Cat.Bi.Univalent
open import Cat.Displayed.Total
open import Cat.Displayed.Functor
open import Cat.Displayed.Functor.Univalence
open import Cat.Functor.Univalence
open import Cat.Bi.Diagram.Adjunction
open import Cat.Displayed.Univalence
open import Cat.Displayed.Univalence.Reasoning
open import Cat.Bi.AdjointEquiv
open import Cat.Functor.Adjoint.Unique
open import Cat.Displayed.Functor
open import Cat.Functor.Equivalence.Path

import Cat.Functor.Equivalence as FunEquiv
import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr
open import Cat.Univalent
import Cat.Functor.Bifunctor as Bi

module Cat.Bi.Univalent.Instances.MultiCats (o ℓ : Level) where

open import Cat.Bi.Instances.Multi o ℓ
open import Cat.Bi.Univalent.Instances.Cats o ℓ

open Prebicategory
module Multi = Prebicategory Multicats
open Multicat using (disp)

import Cat.Morphism as Cm

private module _ where
    open MultiFunctor
    open make-natural-iso
    open Functor
    open _=>↓_
    assoc : Associator-for {O = Σ[ M ∈ Multicat o ℓ ] is-category-displayed (M .disp)} (λ M N → Multi.Hom (M .fst) (N .fst)) Multi.compose
    assoc {C = C} {D} = to-natural-iso ni where
      module D = Multicat (D .fst)
      module C = Multicat (C .fst)
      module D' {x} = Cr (Fibre D.disp x)
      module C' {x} = Cr (Fibre C.disp x)


      ni : make-natural-iso {D = MultiFunctors _ _} _ _
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

Univalent-Multicat : Prebicategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Univalent-Multicat .Ob = Σ[ M ∈ Multicat o ℓ ] is-category-displayed (M .disp)
Univalent-Multicat .Hom (C , _ ) (D , _) = Multi.Hom C D
Univalent-Multicat .id = Multi.id
Univalent-Multicat .compose = Multi.compose
Univalent-Multicat .unitor-l = Multi.unitor-l
Univalent-Multicat .unitor-r = Multi.unitor-r
Univalent-Multicat .associator = assoc
Univalent-Multicat .triangle f g = reext! (Multi.triangle f g)
Univalent-Multicat .pentagon f g h i = reext! (Multi.pentagon f g h i)

open Dist

open is-bicategory
open MultiFunctor
open _=>↓_
Univalent-Multicat-is-local-bicategory : is-local-bicategory Univalent-Multicat
Univalent-Multicat-is-local-bicategory (A , _) (B , univ) = equiv-path→identity-system $ λ {F} {G} →
  F M[A,B].≅ G
  ≃⟨ Iso→Equiv (
    {- to -} (λ x → record { M[A,B]._≅_ x; inverses = record { M[A,B].Inverses (x .M[A,B]._≅_.inverses)  } }) , record where
    from x = record { [A,B]._≅_ x; inverses = record { [A,B].Inverses (x .[A,B]._≅_.inverses)  } }
    rinv x = trivial!
    linv x = trivial!
  )⟩
  F .U [A,B].≅ G .U
  ≃⟨ identity-system-gives-path $ Vertical-functor-is-category A.disp B.disp univ ⟩
  F .U ≡ G .U
  ≃⟨ identity-system-gives-path $ pullback-identity-system Path-identity-system $
    (Iso→Embedding $ MultiFunctor-iso A B) ∙emb (fst , Subset-proj-embedding λ F → hlevel 1) ⟩
  F ≡ G
  ≃∎ where
  module local where
  module A = Multicat A
  module B = Multicat B
  module M[A,B] = Cr (MultiFunctors A B)
  module [A,B] = Cr (Cat↓[ A.disp , B.disp ])
