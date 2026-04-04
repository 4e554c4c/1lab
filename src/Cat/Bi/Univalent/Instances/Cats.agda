
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

import Cat.Functor.Bifunctor as Bi
import Cat.Reasoning as Cr
import Cat.Univalent
import Cat.Functor.Equivalence as FunEquiv
import Cat.Functor.Reasoning as Fr
import Cat.Natural.Reasoning

module Cat.Bi.Univalent.Instances.Cats (o ℓ : Level) where

open Prebicategory

module Cat = Prebicategory (Cat o ℓ)
private module _ where
  open Functor
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

Univalent-Cat : Prebicategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Univalent-Cat .Ob = Σ[ C ∈ Precategory o ℓ ] is-category C
Univalent-Cat .Hom (C , _ ) (D , _) = Cat.Hom C D
Univalent-Cat .id = Cat.id
Univalent-Cat .compose = Cat.compose
Univalent-Cat .unitor-l = Cat.unitor-l
Univalent-Cat .unitor-r = Cat.unitor-r
Univalent-Cat .associator = assoc
Univalent-Cat .triangle f g = reext! (Cat.triangle f g)
Univalent-Cat .pentagon f g h i = reext! (Cat.pentagon f g h i)

module _ {C' D' : Univalent-Cat .Ob} where
  --open adjoint-equivalence
  open Σ C' renaming (fst to C)
  open Σ D' renaming (fst to D)
  private
    module C = Cr C
    module D = Cr D
  open Functor
  --open FunEquiv.Equivalence

  bi-eqv≃cat-eqv : (adjoint-equivalence Univalent-Cat C' D') ≃ FunEquiv.Equivalence C D
  bi-eqv≃cat-eqv .fst adj = record { To = adj.To ; To-equiv = record
    { F⁻¹ = adj.From
    ; F⊣F⁻¹ = record
      { unit = adj.η
      ; counit = adj.ε
      ; zig = λ { {A} →
        ε (adj.To · A) D.∘ adj.To .F₁ (η A)
        ≡⟨ cat! D ⟩
        D.id D.∘ ε (adj.To .F₀ A) D.∘ D.id D.∘ adj.To .F₁ (η A) D.∘ D.id
        ≡˘⟨ adj.zig ηₚ A ⟩
        D.id ∎
      }
      ; zag = λ { {B} →
        adj.From .F₁ (ε B) C.∘ (η $ adj.From · B)
        ≡⟨ cat! C ⟩
        C.id C.∘ adj.From .F₁ (ε B) C.∘ C.id C.∘ η (adj.From .F₀ B) C.∘ C.id
        ≡˘⟨ adj.zag ηₚ B ⟩
        C.id ∎
      }
      }
    ; unit-iso = is-invertibleⁿ→is-invertible (adj.unit-iso)
    ; counit-iso = is-invertibleⁿ→is-invertible (adj.counit-iso)
    } }
    where
      module adj = adjoint-equivalence adj
      module eta = Cat.Natural.Reasoning adj.η
      module eps = Cat.Natural.Reasoning adj.ε renaming (η to ε)
      open eta using (η)
      open eps using (ε)
  bi-eqv≃cat-eqv .snd = is-iso→is-equiv blargh where
    open is-iso
    blargh : is-iso (bi-eqv≃cat-eqv .fst)
    blargh .from eqv = record
      { To = eqv.To
      ; is-adj-equiv = record
        { From = eqv.From
        ; adjoint = record
          { η = eqv.unit
          ; ε = eqv.counit
          ; zig = ext λ A →
            D.id
            ≡˘⟨ eqv.zig ⟩
            ε (To.₀ A) D.∘ To.₁ (η A)
            ≡⟨ cat! D ⟩
            D.id D.∘ ε (To.₀ A) D.∘ D.id D.∘ To.₁ (η A) D.∘ D.id
            ∎
          ; zag = ext λ B →
            C.id
            ≡˘⟨ eqv.zag ⟩
            From.₁ (ε B) C.∘ (η $ From.₀ B)
            ≡⟨ cat! C ⟩
            C.id C.∘ From.₁ (ε B) C.∘ C.id C.∘ η (From.₀ B) C.∘ C.id
            ∎
          }
        ; unit-iso = invertible→invertibleⁿ _ $ eqv.unit-iso
        ; counit-iso = invertible→invertibleⁿ _ $ eqv.counit-iso
        }
      } where
        open module eqv = FunEquiv.Equivalence eqv
        open eqv.counit using (ε)
        open eqv.unit using (η)
    blargh .rinv _ = FunEquiv.Equivalence-path refl $ is-equivalence-is-prop (C' .snd) _ _ _
    blargh .linv x = adjoint-equiv-path _ refl $ is-equivalence-path _ refl $ ⊣-path Univalent-Cat refl refl

open is-bicategory
Univalent-Cat-is-bicategory : is-bicategory Univalent-Cat
Univalent-Cat-is-bicategory .is-local _ (_ , univ) = Functor-is-category univ
Univalent-Cat-is-bicategory .is-global = equiv-path→identity-system $ λ {a} {b} →
  adjoint-equivalence Univalent-Cat a b
  ≃⟨ bi-eqv≃cat-eqv ⟩
  FunEquiv.Equivalence (a .fst) (b .fst)
  ≃⟨ Iso→Equiv FunEquiv.Equivalence-iso ⟩
  Σ[ f ∈  Functor (a .fst) (b .fst) ] FunEquiv.is-equivalence f
  ≃⟨ identity-system-gives-path Category-identity-system ⟩
  a ≡ b
  ≃∎
