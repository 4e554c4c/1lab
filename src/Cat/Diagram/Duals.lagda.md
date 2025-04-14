<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Diagram.Colimit.Cocone
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Limit.Cone
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Equaliser
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Diagram.Product
open import Cat.Diagram.Pushout
open import Cat.Prelude
open import Cat.Base
```
-->

```agda
module Cat.Diagram.Duals where
```

<!--
```agda
private
  variable
    o' ℓ' : Level
module _ {o ℓ} {C : Precategory o ℓ} where
  private
    module C = Precategory C
```
-->

# Dualities of diagrams

Following [Hu and Carette][agda-categories], we've opted to have
_different_ concrete definitions for diagrams and their opposites. In
particular, we have the following pairs of "redundant" definitions:

[agda-categories]: https://arxiv.org/abs/2005.07059

- [[Products]] and coproducts
- [[Pullbacks]] and pushouts
- [[Equalisers]] and coequalisers
- [[Terminal objects]] and initial objects

For all four of the above pairs, we have that one in $C$ is the other in
$C\op$. We prove these correspondences here:

## Co/products

```agda
  is-co-product→is-coproduct
    : ∀ {A B P} {i1 : C.Hom A P} {i2 : C.Hom B P}
    → is-product (C ^op) i1 i2 → is-coproduct C i1 i2
  is-co-product→is-coproduct isp =
    record
      { [_,_]      = isp.⟨_,_⟩
      ; []∘ι₁ = isp.π₁∘⟨⟩
      ; []∘ι₂ = isp.π₂∘⟨⟩
      ; unique     = isp.unique
      }
    where module isp = is-product isp

  is-coproduct→is-co-product
    : ∀ {A B P} {i1 : C.Hom A P} {i2 : C.Hom B P}
    → is-coproduct C i1 i2 → is-product (C ^op) i1 i2
  is-coproduct→is-co-product iscop =
    record
      { ⟨_,_⟩     = iscop.[_,_]
      ; π₁∘⟨⟩ = iscop.[]∘ι₁
      ; π₂∘⟨⟩ = iscop.[]∘ι₂
      ; unique    = iscop.unique
      }
    where module iscop = is-coproduct iscop
```

## Co/equalisers

```agda
  is-co-equaliser→is-coequaliser
    : ∀ {A B E} {f g : C.Hom A B} {coeq : C.Hom B E}
    → is-equaliser (C ^op) f g coeq → is-coequaliser C f g coeq
  is-co-equaliser→is-coequaliser eq =
    record
      { coequal    = eq.equal
      ; universal  = eq.universal
      ; factors    = eq.factors
      ; unique     = eq.unique
      }
    where module eq = is-equaliser eq

  is-coequaliser→is-co-equaliser
    : ∀ {A B E} {f g : C.Hom A B} {coeq : C.Hom B E}
    → is-coequaliser C f g coeq → is-equaliser (C ^op) f g coeq
  is-coequaliser→is-co-equaliser coeq =
    record
      { equal     = coeq.coequal
      ; universal = coeq.universal
      ; factors   = coeq.factors
      ; unique    = coeq.unique
      }
    where module coeq = is-coequaliser coeq
```

## Initial/terminal

```agda
  open Terminal
  open Initial

  is-coterminal→is-initial
    : ∀ {A} → is-terminal (C ^op) A → is-initial C A
  is-coterminal→is-initial x = x

  is-initial→is-coterminal
    : ∀ {A} → is-initial C A → is-terminal (C ^op) A
  is-initial→is-coterminal x = x

  Coterminal→Initial : Terminal (C ^op) → Initial C
  Coterminal→Initial term .bot = term .top
  Coterminal→Initial term .has⊥ = is-coterminal→is-initial (term .has⊤)

  Initial→Coterminal : Initial C → Terminal (C ^op)
  Initial→Coterminal init .top = init .bot
  Initial→Coterminal init .has⊤ = is-initial→is-coterminal (init .has⊥)
```

## Pullback/pushout

```agda
  is-co-pullback→is-pushout
    : ∀ {P X Y Z} {p1 : C.Hom X P} {f : C.Hom Z X} {p2 : C.Hom Y P} {g : C.Hom Z Y}
    → is-pullback (C ^op) p1 f p2 g → is-pushout C f p1 g p2
  is-co-pullback→is-pushout pb =
    record
      { square       = pb.square
      ; universal    = pb.universal
      ; universal∘i₁ = pb.p₁∘universal
      ; universal∘i₂ = pb.p₂∘universal
      ; unique       = pb.unique
      }
    where module pb = is-pullback pb

  is-pushout→is-co-pullback
    : ∀ {P X Y Z} {p1 : C.Hom X P} {f : C.Hom Z X} {p2 : C.Hom Y P} {g : C.Hom Z Y}
    → is-pushout C f p1 g p2 → is-pullback (C ^op) p1 f p2 g
  is-pushout→is-co-pullback po =
    record
      { square       = po.square
      ; universal    = po.universal
      ; p₁∘universal = po.universal∘i₁
      ; p₂∘universal = po.universal∘i₂
      ; unique       = po.unique
      }
    where module po = is-pushout po
```

## Co/cones

```agda
  module _ {o ℓ} {J : Precategory o ℓ} {F : Functor J C} where
    open Functor F renaming (op to F^op)

    open Cocone-hom
    open Cone-hom
    open Cocone
    open Cone

    Co-cone→Cocone : Cone F^op → Cocone F
    Co-cone→Cocone cone .coapex = cone .apex
    Co-cone→Cocone cone .ψ = cone .ψ
    Co-cone→Cocone cone .commutes = cone .commutes

    Cocone→Co-cone : Cocone F → Cone F^op
    Cocone→Co-cone cone .apex     = cone .coapex
    Cocone→Co-cone cone .ψ        = cone .ψ
    Cocone→Co-cone cone .commutes = cone .commutes

    Cocone→Co-cone→Cocone : ∀ K → Co-cone→Cocone (Cocone→Co-cone K) ≡ K
    Cocone→Co-cone→Cocone K i .coapex = K .coapex
    Cocone→Co-cone→Cocone K i .ψ = K .ψ
    Cocone→Co-cone→Cocone K i .commutes = K .commutes

    Co-cone→Cocone→Co-cone : ∀ K → Cocone→Co-cone (Co-cone→Cocone K) ≡ K
    Co-cone→Cocone→Co-cone K i .apex = K .apex
    Co-cone→Cocone→Co-cone K i .ψ = K .ψ
    Co-cone→Cocone→Co-cone K i .commutes = K .commutes

    Co-cone-hom→Cocone-hom
      : ∀ {x y}
      → Cone-hom F^op y x
      → Cocone-hom F (Co-cone→Cocone x) (Co-cone→Cocone y)
    Co-cone-hom→Cocone-hom ch .hom = ch .hom
    Co-cone-hom→Cocone-hom ch .commutes o = ch .commutes o

    Cocone-hom→Co-cone-hom
      : ∀ {x y}
      → Cocone-hom F x y
      → Cone-hom F^op (Cocone→Co-cone y) (Cocone→Co-cone x)
    Cocone-hom→Co-cone-hom ch = record { Cocone-hom ch }
```

## Co/limits

Limits and colimits are defined via [[Kan extensions]], so it's reasonable
to expect that [duality of Kan extensions] would apply to (co)limits.
Unfortunately, proof assistants: (co)limits are extensions of
`!F`{.Agda}, but duality of Kan extensions inserts an extra `Functor.op`.
We could work around this, but it's easier to just do the proofs by hand.

[duality of Kan extensions]: Cat.Functor.Kan.Duality.html

```agda
    Colimit→Co-limit
      : Colimit F → Limit F^op
    Colimit→Co-limit colim = to-limit (to-is-limit ml) where
      module colim = Colimit colim
      open make-is-limit

      ml : make-is-limit F^op colim.coapex
      ml .ψ = colim.ψ
      ml .commutes = colim.commutes
      ml .universal eps p = colim.universal eps p
      ml .factors eps p = colim.factors eps p
      ml .unique eps p other q = colim.unique eps p other q

    Co-limit→Colimit
      : Limit F^op → Colimit F
    Co-limit→Colimit lim = to-colimit (to-is-colimit mc) where
      module lim = Limit lim
      open make-is-colimit

      mc : make-is-colimit F lim.apex
      mc .ψ = lim.ψ
      mc .commutes = lim.commutes
      mc .universal eta p = lim.universal eta p
      mc .factors eta p = lim.factors eta p
      mc .unique eta p other q = lim.unique eta p other q
    is-cocontinuous→co-is-continuous
      : is-cocontinuous o' ℓ' F → is-continuous o' ℓ' F^op
    is-cocontinuous→co-is-continuous = ?

module _ {o ℓ} {C : Precategory o ℓ} where
  co-is-cocomplete→is-cocomplete : is-complete o' ℓ' (C ^op) → is-cocomplete o' ℓ' C
  co-is-cocomplete→is-cocomplete co-complete F = Co-limit→Colimit $ co-complete $ Functor.op F

  is-cocomplete→co-is-complete : is-cocomplete o' ℓ' (C ^op) → is-complete o' ℓ' C
  is-cocomplete→co-is-complete cocomplete F = Colimit→Co-limit $ cocomplete $ Functor.op  F

```
