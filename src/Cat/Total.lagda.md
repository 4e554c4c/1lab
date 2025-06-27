<!--
```agda
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Adjoint.Reflective
open import Cat.Diagram.Initial
open import Cat.Instances.Comma
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Adjoint.AFT
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Naturality
open import Cat.Instances.Functor
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Diagram.Duals
open import Cat.Functor.Base
open import Cat.Functor.Hom.Representable
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Hom.Duality
open import Cat.Prelude
open import Cat.Functor.Kan.Nerve
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

## Free objects relative to よ

Before we investigate the properties of a total category, it's worth
considering the action of such a functor on objects, if it exists. Given
some presheaf $$F\in\psh(\cC)$$, an object could be $れ(F)$ if it is [[free|universal morphism]]
with respect to $\yo$.

```agda
module _ (F : Functor (C ^op) (Sets ℓ)) (c : Free-object よ F) where
```
<!--
```agda
  open Free-object c
  private
```
-->

Such an object is initial in the [[comma category]] $F \swarrow よ$*
```
    initial-comma : Initial (F ↙ よ)
    initial-comma = free-object→universal-map c

```

<!--
```agda
module _ (C-total : is-total) where
  open module C-total = is-total C-total

  れ∘よ≅ⁿid : れ F∘ よ ≅ⁿ Id
  れ∘よ≅ⁿid = is-reflective→counit-iso has-よ-adj よ-is-fully-faithful
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
  cocontinuous→right-adjoint {D = D} F F-is-cocont = G , F⊣G where
    module F = Functor F
    module D = Precategory D
    open import Cat.Functor.Hom D using () renaming (Hom-into to Hom-intoᴰ; よ to よᴰ )

    G : Functor D C
    G = れ F∘ Nerve F
    module G = Functor G

    open _⊣_
    F⊣G : F ⊣ G
    F⊣G .unit = ni-assoc .Isoⁿ.to ∘nt (れ ▸ coapprox F) ∘nt れ∘よ≅ⁿid .Isoⁿ.from
    --F⊣G .counit = {! !}
    F⊣G .counit ._=>_.η d = {! !}
    F⊣G .counit ._=>_.is-natural x y f = {! !}
    F⊣G .zig = {! !}
    F⊣G .zag = {! !}
```
