<!--
```agda
open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Functor.Compose
open import Cat.Functor.Naturality
open import Cat.Instances.Functor
open import Cat.Functor.Adjoint
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Duals
open import Cat.Functor.Adjoint.AFT
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Adjoint.Reflective
```
-->

```agda
module Cat.Total {o ℓ} (C : Precategory o ℓ) where
open import Cat.Functor.Hom C
open import Cat.Instances.Presheaf.Colimits
```
<!--
```agda
private
  open module C = Precategory C
  variable
    o' ℓ' : Level
```
-->

# Total precategories {defines="total-precategory"}

A precategory is **total** if its yoneda embedding has a left adjoint.

```agda
record is-total : Type (o ⊔ lsuc ℓ) where
  field
    {れ} : Functor Cat[ C ^op , Sets ℓ ] C
    has-よ-adj : れ ⊣ よ
```
<!--
```agda
module _ (C-total : is-total) where
  open module C-total = is-total C-total
```
-->

## Cocompleteness

All total categories are [[cocomplete]].

```agda
  total→cocomplete : is-cocomplete ℓ ℓ C
  total→cocomplete F = natural-iso→colimit ni $ left-adjoint-colimit has-よ-adj $ Psh-cocomplete ℓ C (よ F∘ F)
    where ni : れ F∘ よ F∘ F ≅ⁿ F
          ni = ni-assoc ∙ni
            (is-reflective→counit-iso has-よ-adj よ-is-fully-faithful ◂ni F) ∙ni
            path→iso F∘-idl
```

## The adjoint functor property

Total precategories satisfy a particularly nice [[adjoint functor theorem]]. In
particular, every [[continuous functor]] $F$ has a [[left adjoint]].



```agda
  cocontinuous→right-adjoint : ∀ {D : Precategory ℓ ℓ}
    (F : Functor C D) → is-cocontinuous ℓ ℓ F → Σ[ G ∈ Functor D C ] F ⊣ G
  cocontinuous→right-adjoint {D = D} F F-is-cocont = G , opposite-adjunction Gᵒᵖ⊣Fᵒᵖ
    where module F = Functor F
          module D = Precategory D
          open import Cat.Functor.Hom D using () renaming (Hom-into to Hom-intoᴰ; よ to よᴰ )

          my-silly-presheaf : D.Ob → ⌞ PSh ℓ C ⌟
          my-silly-presheaf y = Hom-intoᴰ y F∘ F.op

          my-silly-functor : Functor D C
          my-silly-functor = れ F∘ precompose F.op  F∘ よᴰ
          module my-silly-functor = Functor my-silly-functor

          op-adj : Σ[ G ∈ Functor (D ^op) (C ^op) ] G ⊣ F.op
          op-adj = solution-set→left-adjoint F.op (is-cocomplete→co-is-complete total→cocomplete) (is-cocontinuous→co-is-continuous F-is-cocont) λ y →
            record { index = Lift _ ⊤
                   ; has-is-set = hlevel 2
                   ; dom = λ _ → my-silly-functor.₀ y
                   ; map = λ _ → {! !}
                   ; factor = λ h → do
                      pure $ {! !} , {! !} , {! !}
                   }
          G = Functor.op $ op-adj .fst
          Gᵒᵖ⊣Fᵒᵖ = op-adj .snd
```
