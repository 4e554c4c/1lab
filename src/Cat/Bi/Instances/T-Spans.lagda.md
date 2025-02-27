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
module Cat.Bi.Instances.T-Spans {o ℓ} {C : Precategory o ℓ} (T : CartesianMonad C) where

private
  open module C = Cat.Reasoning C
  module T = CartesianMonad T


record Span (a b : Ob) : Type (o ⊔ ℓ) where
  constructor t-span
  field
    apex  : Ob
    left  : Hom apex (T.M₀ a)
    right : Hom apex b

open Span

record Span-hom {a b : Ob} (x y : Span a b) : Type ℓ where
  no-eta-equality
  field
    map   : Hom (x .apex) (y .apex)
    left  : x .left  ≡ y .left ∘ map
    right : x .right ≡ y .right ∘ map


open Span-hom
unquoteDecl H-Level-Span-hom = declare-record-hlevel 2 H-Level-Span-hom (quote Span-hom)

instance
  Underlying-Span : ∀ {a b} ⦃ _ : Underlying Ob ⦄ → Underlying (Span a b)
  Underlying-Span = record { ⌞_⌟ = λ S → ⌞ S .apex ⌟ }

Span-hom-path
  : {a b : Ob} {x y : Span a b} {f g : Span-hom x y}
  → f .map ≡ g .map → f ≡ g
Span-hom-path p i .map = p i
Span-hom-path {x = x} {y} {f} {g} p i .left j =
  is-set→squarep (λ i j → Hom-set _ _)
    (λ _ → x .left) (λ j → f .left j) (λ j → g .left j) (λ j → y .left ∘ p j) i j
Span-hom-path {x = x} {y} {f} {g} p i .right j =
  is-set→squarep (λ i j → Hom-set _ _)
    (λ _ → x .right) (λ j → f .right j) (λ j → g .right j) (λ j → y .right ∘ p j) i j


Spans : Ob → Ob → Precategory _ _
Spans x y .Precategory.Ob = Span x y
Spans x y .Precategory.Hom = Span-hom
Spans x y .Precategory.Hom-set _ _ = hlevel 2
Spans x y .Precategory.id .map = id
Spans x y .Precategory.id .left = intror refl
Spans x y .Precategory.id .right = intror refl
Spans x y .Precategory._∘_ f g .map = f .map ∘ g .map
Spans x y .Precategory._∘_ f g .left = g .left ∙ pushl (f .left)
Spans x y .Precategory._∘_ f g .right = g .right ∙ pushl (f .right)
Spans x y .Precategory.idr f = Span-hom-path (idr _)
Spans x y .Precategory.idl f = Span-hom-path (idl _)
Spans x y .Precategory.assoc f g h = Span-hom-path (assoc _ _ _)

Span-id : ∀ {a} → Span a a
Span-id {a} .apex = a
Span-id {a} .left = T.η a
Span-id .right = id

module _ (pb : ∀ {a b c} (f : Hom a b) (g : Hom c b) → Pullback C f g) where
  open Functor

  Span-∘ : ∀ {a b c} → Functor (Spans b c ×ᶜ Spans a b) (Spans a c)
  Span-∘ .F₀ (sp1 , sp2) = t-span pb.apex (T.μ _ ∘ T.₁ (sp2 .left) ∘ pb.p₂) (sp1 .right ∘ pb.p₁)
     where module pb = Pullback (pb (sp1 .left) (T.₁ (sp2 .right)))
  Span-∘ .F₁ {x1 , x2} {y1 , y2} (f , g) = res
    where
      module x = Pullback (pb (x1 .left) (T.M₁ (x2 .right)))
      module y = Pullback (pb (y1 .left) (T.M₁ (y2 .right)))
      x→y : Hom x.apex y.apex
      x→y = y.universal {p₁' = f .map ∘ x.p₁} {p₂' = T.M₁ (g .map) ∘ x.p₂} comm
        where abstract
          open Pullback
          comm : y1 .left ∘ f .map ∘ x.p₁ ≡ T.M₁ (y2 .right) ∘ T.M₁ (g .map) ∘ x.p₂
          comm = pulll (sym (f .left)) ∙ x.square ∙ (pushl $ T.expand $ g .right)
      res : Span-hom (Span-∘ .F₀ (x1 , x2))  (Span-∘ .F₀ (y1 , y2))
      res .map = x→y
      res .left = T.μ _ ∘ T.₁ (x2 .left) ∘ x.p₂                     ≡⟨ refl⟩∘⟨ pushl (T.expand (g .left)) ⟩
                  T.μ _ ∘ T.₁ (y2 .left) ∘ T.M₁ (g .map) ∘ x.p₂     ≡˘⟨ refl⟩∘⟨ pullr y.p₂∘universal  ⟩
                  T.μ _ ∘ (T.₁ (y2 .left) ∘ pb.p₂) ∘ pb.universal _ ≡⟨ assoc _ _ _  ⟩
                  (T.μ _ ∘ T.₁ (y2 .left) ∘ pb.p₂) ∘ pb.universal _ ∎
        where module pb = Pullback (pb (y1 .left) (T.₁ (y2 .right)))
      res .right = sym (pullr y.p₁∘universal ∙ pulll (sym (f .right)))

  Span-∘ .F-id {x1 , x2} = Span-hom-path $ sym $ x.unique id-comm (idr x.p₂ ∙ (sym $ eliml T.M-id))
    where module x = Pullback (pb (x1 .left) (T.₁ (x2 .right)))

  Span-∘ .F-∘ {x1 , x2} {y1 , y2} {z1 , z2} f g =
    Span-hom-path $ sym $ z.unique
      (pulll z.p₁∘universal ∙ pullr y.p₁∘universal ∙ assoc _ _ _)
      (pulll z.p₂∘universal ∙ pullr y.p₂∘universal ∙ assoc _ _ _ ∙ (sym $ T.M-∘ _ _ ⟩∘⟨refl))
    where
      module x = Pullback (pb (x1 .left) (T.₁ (x2 .right)))
      module y = Pullback (pb (y1 .left) (T.₁ (y2 .right)))
      module z = Pullback (pb (z1 .left) (T.₁ (z2 .right)))

  --open Prebicategory
  open Pullback

  private
    _¤_ : ∀ {a b c} (x : Span b c) (y : Span a b) → Span a c
    f ¤ g = Span-∘ .F₀ (f , g)

    sλ← : ∀ {A B} (x : Span A B) → Span-hom x (Span-id ¤ x)
    sλ← {A} {B} x = hom where
      module pb = Pullback (pb (T.η B) (T.₁ (x .right)))
      hom : Span-hom x (Span-id ¤ x)
      hom .map = pb.universal {p₂' = T.η (x .apex)} $ T.unit.is-natural (x .apex) _ (x .right)
      hom .right = sym $ pullr pb.p₁∘universal ∙ idl _
      hom .left =
        x .left ≡⟨ {! !} ⟩
        T.μ _ ∘ T.₁ (x .left) ∘ T.η (x .apex)  ≡⟨ {! !} ⟩
        T.μ _ ∘ T.₁ (x .left) ∘ pb.p₂ ∘ pb.universal _ ≡⟨ {! !} ⟩
        (T.μ _ ∘ T.₁ (x .left) ∘ pb.p₂) ∘ pb.universal _ ∎
{-
    sλ← {A} {B} x .map   = pb (T.η B) (T.₁ (x .right)) .universal
    sλ← x .left  =  {! sym $ pullr (pb _ _ .p₂∘universal) ∙ idr _ !}
      --x .left ≡⟨ ? ⟩
      --(T.η _ ∘ T.₁ (x .left) ∘ (pb.p₂ (T.η _) (T.₁ (x .right)))) ∘ pb.universal _ ∎
      --where module pb = Pullback ? ?
    sλ← x .right = sym $ pullr (pb _ _ .p₁∘universal) ∙ idl _
-}

    sρ← : ∀ {A B} (x : Span A B) → Span-hom x (x ¤ Span-id)
    sρ← {A} {B} x = hom where
      module pb = Pullback (pb (x .left) (T.₁ id))
      hom : Span-hom x (x ¤ Span-id)
      hom .map   = pb.universal $ id-comm ∙ ap (_∘ x .left) (sym T.M-id)
      hom .left  = {! sym $ pullr (pb _ _ .p₂∘universal) ∙ idl _ !}
      hom .right = sym $ pullr pb.p₁∘universal ∙ idr _


  open Prebicategory
  Spanᵇ : Prebicategory _ _ _
  Spanᵇ .Ob = C.Ob
  Spanᵇ .Hom = Spans
  Spanᵇ .id = Span-id
  Spanᵇ .compose = Span-∘
  Spanᵇ .unitor-l = {! !}
  Spanᵇ .unitor-r = {! !}
  Spanᵇ .associator = {! !}
  Spanᵇ .triangle f g = {! !}
  Spanᵇ .pentagon f g h i = {! !}




```

