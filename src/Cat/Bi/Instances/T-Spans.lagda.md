<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Diagram.Pullback
open import Cat.Diagram.Monad.Pullback
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Reasoning
import Cat.Functor.Reasoning
```
-->

```agda
module Cat.Bi.Instances.T-Spans {o ℓ} (C : Precategory o ℓ) (T : CartesianMonad C) where

private
  open module C = Cat.Reasoning C
  module T where
    open CartesianMonad T public
    open Cat.Functor.Reasoning M public


record T-Span (a b : Ob) : Type (o ⊔ ℓ) where
  constructor t-span
  field
    apex  : Ob
    left  : Hom apex (T.M₀ a)
    right : Hom apex b

open T-Span

record T-Span-hom {a b : Ob} (x y : T-Span a b) : Type ℓ where
  no-eta-equality
  field
    map   : Hom (x .apex) (y .apex)
    left  : x .left  ≡ y .left ∘ map
    right : x .right ≡ y .right ∘ map


open T-Span-hom
unquoteDecl H-Level-T-Span-hom = declare-record-hlevel 2 H-Level-T-Span-hom (quote T-Span-hom)

instance
  Underlying-T-Span : ∀ {a b} ⦃ _ : Underlying Ob ⦄ → Underlying (T-Span a b)
  Underlying-T-Span = record { ⌞_⌟ = λ S → ⌞ S .apex ⌟ }

T-Span-hom-path
  : {a b : Ob} {x y : T-Span a b} {f g : T-Span-hom x y}
  → f .map ≡ g .map → f ≡ g
T-Span-hom-path p i .map = p i
T-Span-hom-path {x = x} {y} {f} {g} p i .left j =
  is-set→squarep (λ i j → Hom-set _ _)
    (λ _ → x .left) (λ j → f .left j) (λ j → g .left j) (λ j → y .left ∘ p j) i j
T-Span-hom-path {x = x} {y} {f} {g} p i .right j =
  is-set→squarep (λ i j → Hom-set _ _)
    (λ _ → x .right) (λ j → f .right j) (λ j → g .right j) (λ j → y .right ∘ p j) i j


T-Spans : Ob → Ob → Precategory _ _
T-Spans x y .Precategory.Ob = T-Span x y
T-Spans x y .Precategory.Hom = T-Span-hom
T-Spans x y .Precategory.Hom-set _ _ = hlevel 2
T-Spans x y .Precategory.id .map = id
T-Spans x y .Precategory.id .left = intror refl
T-Spans x y .Precategory.id .right = intror refl
T-Spans x y .Precategory._∘_ f g .map = f .map ∘ g .map
T-Spans x y .Precategory._∘_ f g .left = g .left ∙ pushl (f .left)
T-Spans x y .Precategory._∘_ f g .right = g .right ∙ pushl (f .right)
T-Spans x y .Precategory.idr f = T-Span-hom-path (idr _)
T-Spans x y .Precategory.idl f = T-Span-hom-path (idl _)
T-Spans x y .Precategory.assoc f g h = T-Span-hom-path (assoc _ _ _)

T-Span-id : ∀ {a} → T-Span a a
T-Span-id {a} .apex = a
T-Span-id {a} .left = T.η a
T-Span-id .right = id

module _ (pb : ∀ {a b c} (f : Hom a b) (g : Hom c b) → Pullback C f g) where
  open Functor


  T-Span-∘ : ∀ {a b c} → Functor (T-Spans b c ×ᶜ T-Spans a b) (T-Spans a c)
  T-Span-∘ .F₀ (sp1 , sp2) = t-span pb.apex (T.μ _ ∘ T.M₁ (sp2 .left) ∘ pb.p₂) (sp1 .right ∘ pb.p₁)
     where module pb = Pullback (pb (sp1 .left) (T.M₁ (sp2 .right)))
  T-Span-∘ .F₁ {x1 , x2} {y1 , y2} (f , g) = res
    where
      module x = Pullback (pb (x1 .left) (T.M₁ (x2 .right)))
      module y = Pullback (pb (y1 .left) (T.M₁ (y2 .right)))

      x→y : Hom x.apex y.apex
      x→y = y.universal {p₁' = f .map ∘ x.p₁} {p₂' = T.M₁ (g .map) ∘ x.p₂} comm
        where abstract
          open Pullback
          comm : y1 .left ∘ f .map ∘ x.p₁ ≡ T.M₁ (y2 .right) ∘ T.M₁ (g .map) ∘ x.p₂
          comm = pulll (sym (f .left)) ∙ x.square ∙ (pushl $ T.expand $ g .right)

      {-

      -}
      res : T-Span-hom (T-Span-∘ .F₀ (x1 , x2))  (T-Span-∘ .F₀ (y1 , y2))
      res .map = x→y
      --res .left = sym (pullr y.p₂∘universal ∙  pulll (sym (g .left)))
      res .left = {! sym (pullr y.p₂∘universal ∙ ? )  !}
      res .right = sym (pullr y.p₁∘universal ∙ pulll (sym (f .right)))

  T-Span-∘ .F-id {x1 , x2} = T-Span-hom-path $ sym $ x.unique id-comm (idr x.p₂ ∙ (sym $ eliml T.F-id))
    where module x = Pullback (pb (x1 .left) (T.F₁ (x2 .right)))

  T-Span-∘ .F-∘ {x1 , x2} {y1 , y2} {z1 , z2} f g =
    T-Span-hom-path $ sym $ z.unique
      (pulll z.p₁∘universal ∙ pullr y.p₁∘universal ∙ assoc _ _ _)
      (pulll z.p₂∘universal ∙ pullr y.p₂∘universal ∙ assoc _ _ _ ∙ (sym $ T.F-∘ _ _ ⟩∘⟨refl))
    where
      module x = Pullback (pb (x1 .left) (T.F₁ (x2 .right)))
      module y = Pullback (pb (y1 .left) (T.F₁ (y2 .right)))
      module z = Pullback (pb (z1 .left) (T.F₁ (z2 .right)))




```

