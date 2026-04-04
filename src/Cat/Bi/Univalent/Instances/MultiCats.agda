
open import Cat.Prelude

open import Cat.Functor.Base
open import Cat.Instances.Simplex.Pointed
open import Cat.Displayed.Multi.Base
open import Cat.Functor.Naturality
open import Cat.Functor.Compose renaming (_◆_ to _◇_)
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base

open import Cat.Bi.Base
open import Cat.Bi.Univalent
open import Cat.Displayed.Total
open import Cat.Displayed.Functor
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

private module _ where
    open MultiFunctor
    open make-natural-iso
    open Functor
    open _=>↓_
    assoc : Associator-for {O = Σ[ M ∈ Multicat o ℓ ] is-category-displayed (M .disp)} (λ M N → MultiFunctors (M .fst) (N .fst)) ∘M-functor
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

open is-bicategory
open MultiFunctor
open _=>↓_
Univalent-Multicat-is-bicategory : is-bicategory Univalent-Multicat
Univalent-Multicat-is-bicategory .is-local (A , _) (B , univ) .to-path {a} {b} i =
  MultiFunctor-path A B (λ x' → vertical-iso→path (B.disp) univ $ isos x') λ {x' = x'} {y'} f' →
    Hom[]-pathp-iso (B.disp) univ (Δ∙.idl _ ∙ Δ∙.idr _) (isos _) (isos _) (a .F₁' f') (b .F₁' f') $ begin[]
    i.to .η' y' ∘' a .F₁' f' ∘' i.from .η' x'
    ≡[]⟨ extendl[] Δ∙.id-comm-sym $ i.to .is-natural' x' y' f' ⟩
    b .F₁' f' ∘' i.to .η' x' ∘' i.from .η' x'
    ≡[]⟨ elimr[] (Δ∙.idr Δ-id) $ to-pathp[] $ i.invl η↓ₚ x' ⟩
    b .F₁' f'
    ∎[]
  where
  module M[A,B] = Cr (MultiFunctors A B)
  module i = M[A,B]._≅_ i
  open module B = Multicat B
  module A = Multicat A
  isos : ∀ {n} (x' : A.Ob[ n ]) → a .F₀' x' B.≅↓ b .F₀' x'
  isos x' = record where
    to' = i.to .η' x'
    from' = i.from .η' x'
    inverses' = record
      { invl' = B.to-pathp[] $ i.invl η↓ₚ x'
      ; invr' = B.to-pathp[] $ i.invr η↓ₚ x'
      }
Univalent-Multicat-is-bicategory .is-local (A , _) (B , univ) .to-path-over i = {! !}

Univalent-Multicat-is-bicategory .is-global .to-path {A , a-cat} {B , b-cat} eqv  = Σ-prop-path! {! !}
