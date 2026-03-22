
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
open import Cat.Functor.Univalence
open import Cat.Bi.Diagram.Adjunction
open import Cat.Displayed.Univalence
open import Cat.Bi.AdjointEquiv
open import Cat.Functor.Adjoint.Unique
open import Cat.Displayed.Functor
open import Cat.Functor.Equivalence.Path

import Cat.Functor.Equivalence as FunEquiv
import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr
import Cat.Univalent
import Cat.Functor.Bifunctor as Bi

module Cat.Bi.Univalent.Instances.MultiCats (o ℓ : Level) where
open import Cat.Bi.Instances.Multi o ℓ
open import Cat.Bi.Univalent.Instances.Cats o ℓ

open Prebicategory
module Multi = Prebicategory Multicats
open Multicat hiding (Ob)

private module _ where
    open MultiFunctor
    open make-natural-iso
    open Functor
    open _=>↓_
    assoc : Associator-for {O = Σ[ M ∈ Multicat o ℓ ] is-category-displayed (M .disp)} (λ M N → MultiFunctors (M .fst) (N .fst)) ∘M-functor
    assoc {D = D} = to-natural-iso ni where
      module D = Multicat (D .fst)
      module D' {x} = Cr (Fibre D.disp x) using (_∘_ ; idl ; idr ; elimr ; pushl ; introl)

      ni : make-natural-iso {D = MultiFunctors _ _} _ _
      ni .eta _ = record { η' = λ x' → D.id' ; is-natural' = λ x y f → D.to-pathp[] D.id-comm[] }
      ni .inv _ = record { η' = λ x' → D.id' ; is-natural' = λ x y f → D.to-pathp[] D.id-comm[] }
      ni .eta∘inv _ = ext λ _ → D'.idl _
      ni .inv∘eta _ = ext λ _ → D'.idl _
      ni .natural x y f = ext λ _ → D'.idr _ ∙∙ D'.pushl (F-∘↓ $ y .fst) ∙∙ D'.introl refl

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
Univalent-Multicat-is-bicategory : is-bicategory Univalent-Multicat
Univalent-Multicat-is-bicategory .is-local (A , _) (B , univ) = {! !}
Univalent-Multicat-is-bicategory .is-global = {! !}
{-equiv-path→identity-system $ λ { {a , uaa} {(b , uab)} →
  adjoint-equivalence Univalent-Multicat (a , uaa) (b , uab)
  ≃⟨ ? ⟩
  adjoint-equivalence Univalent-Cat ((∫ (a .disp)) , is-category-total _ Δ∙-cat uaa) (∫ (b .disp) , is-category-total _ Δ∙-cat uab)
  ≃⟨ identity-system-gives-path $ Univalent-Cat-is-bicategory .is-global ⟩
  (∫ (a .disp) , is-category-total (disp a) Δ∙-cat uaa) ≡ (∫ (b .disp) , is-category-total (disp b) Δ∙-cat uab)
  ≃⟨ ? ⟩
  ∫ (a .disp) ≡ ∫ (b .disp)
  ≃⟨ ? ⟩
  a ≡ b
  ≃⟨ ? ⟩
  (a , _) ≡ (b , _)
  ≃∎ }
  -}
