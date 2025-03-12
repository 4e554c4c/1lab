<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Diagram.Pullback
open import Cat.Diagram.Pullback.Properties
open import Cat.Diagram.Product
open import Cat.Diagram.Terminal
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Monad.Pullback
open import Cat.Bi.Base
open import Cat.Prelude hiding (⊤)
open import Cat.Functor.Bifunctor as Bi

import Cat.Reasoning
import Cat.Functor.Reasoning
```
-->

```agda
module Cat.Bi.Instances.T-Spans {o ℓ} {C : Precategory o ℓ} (T : CartesianMonad C) (term : Terminal C)  where

private
  open module C = Cat.Reasoning C
  module T = CartesianMonad T
  open Terminal term renaming (top to ⊤)


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

Span-hom-id : ∀ {a b} {s : Span a b} → Span-hom s s
Span-hom-id .map = id
Span-hom-id .left = intror refl
Span-hom-id .right = intror refl

Spans : Ob → Ob → Precategory _ _
Spans x y .Precategory.Ob = Span x y
Spans x y .Precategory.Hom = Span-hom
Spans x y .Precategory.Hom-set _ _ = hlevel 2
Spans x y .Precategory.id = Span-hom-id
Spans x y .Precategory._∘_ f g .map = f .map ∘ g .map
Spans x y .Precategory._∘_ f g .left = g .left ∙ pushl (f .left)
Spans x y .Precategory._∘_ f g .right = g .right ∙ pushl (f .right)
Spans x y .Precategory.idr f = Span-hom-path (idr _)
Spans x y .Precategory.idl f = Span-hom-path (idl _)
Spans x y .Precategory.assoc f g h = Span-hom-path (assoc _ _ _)

module Spans x y = Cat.Reasoning (Spans x y)


Span-iso : {A B : Ob} (x y : Span A B) → Type ℓ
Span-iso {A} {B} x y = Spans.Isomorphism A B x y

mk-span-iso : ∀ {A B} {x y : Span A B}
            → (h : Span-hom x y) → is-invertible (h .map)
            → Span-iso x y
mk-span-iso {x = x} {y} h is-inv = i where
  open Inverses
  open _≅_
  open module is-inv = is-invertible is-inv using (inv)
  module h = Span-hom h
  i : Span-iso x y
  i .to = h
  i .from .map = inv
  i .from .left =
    y .left                 ≡⟨ insertr is-inv.invl ⟩
    (y .left ∘ h.map) ∘ inv ≡˘⟨ h .left ⟩∘⟨refl ⟩
    x .left ∘ inv           ∎
  i .from .right =
    y .right                 ≡⟨ insertr is-inv.invl ⟩
    (y .right ∘ h.map) ∘ inv ≡˘⟨ h .right ⟩∘⟨refl ⟩
    x .right ∘ inv           ∎
  i .inverses .invl = Span-hom-path is-inv.invl
  i .inverses .invr = Span-hom-path is-inv.invr

mk-span-iso' : ∀ {A B} {x y : Span A B}
            → (map : x .apex ≅ y .apex)
            → (x .left  ≡ y .left ∘ map .to)
            → (x .right ≡ y .right ∘ map .to)
            → Span-iso x y
mk-span-iso' {x = x} {y} m l r = mk-span-iso (record { map = m .to ; left = l ; right = r }) (iso→invertible m)

Span-id : ∀ {a} → Span a a
Span-id {a} .apex = a
Span-id {a} .left = T.η a
Span-id .right = id

module _ (pb : has-pullbacks C) where
  open Functor
  open Pullbacks C pb

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
  open is-pullback

  module Span-∘ {a b c} = Bi (Span-∘ {a} {b} {c})

  infixr 25 _⊗_ _◆_
  infix 35 _◀_ _▶_

  private
    _⊗_ : ∀ {a b c} (x : Span b c) (y : Span a b) → Span a c
    f ⊗ g = Span-∘.F₀ (f , g)
    _◆_ : ∀ {a b c} {s s' : Span b c} (β : Span-hom s s') {r r' : Span a b} (α : Span-hom r r')
        → Span-hom (s ⊗ r) (s' ⊗  r')
    _◆_ β α = Span-∘.F₁ (β , α)

    -- whiskering on the right
    _▶_ : ∀ {A B C} (f : Span B C) {a b : Span A B} (g : Span-hom a b) → Span-hom (f ⊗ a) (f ⊗ b)
    _▶_ {A} {B} {C} f g = Span-hom-id ◆ g

    -- whiskering on the left
    _◀_ : ∀ {A B C} {a b : Span B C} (g : Span-hom a b) (f : Span A B) → Span-hom (a ⊗ f) (b ⊗ f)
    _◀_ {A} {B} {C} g f = g ◆ Span-hom-id
```

There is no immediate way to draw the left unitor. We need a map from
the pullback $B\times_{TB}Tp$ to $p$. However, since $\eta$ is equifibred,
$p$ too forms pullback with the same cospan as our composition. Thus $p$
is isomorphic

~~~{.quiver}
\[\begin{tikzcd}
	&& p \\
	&& {B\times_{TB}Tp} \\
	& B && Tp \\
	B && TB && {T^2A} & TA
	\arrow["\ell"', curve={height=18pt}, from=1-3, to=3-2]
	\arrow["\eta", curve={height=-18pt}, from=1-3, to=3-4]
	\arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-45}, draw=none, from=1-3, to=4-3]
	\arrow["r"', curve={height=-30pt}, from=1-3, to=4-6]
	\arrow["{\pi_1}"', from=2-3, to=3-2]
	\arrow["{\pi_2}", from=2-3, to=3-4]
	\arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-45}, draw=none, from=2-3, to=4-3]
	\arrow[from=3-2, to=4-1]
	\arrow["\eta", from=3-2, to=4-3]
	\arrow["{T\ell}"', from=3-4, to=4-3]
	\arrow["Tr", from=3-4, to=4-5]
	\arrow["\mu", from=4-5, to=4-6]
\end{tikzcd}\]
~~~

```agda
    sλ≅ : ∀ {A B} (x : Span A B) → Span-iso x (Span-id ⊗ x)
    sλ≅ {A} {B} x = mk-span-iso hom (pullback-unique' pb.has-is-pb x-is-pb) where
      module pb = Pullback (pb (T.η B) (T.₁ (x .right)))
      abstract
        x-is-pb : is-pullback C (x .right) (T.η B) (T.η (x .apex)) (T.₁ (x .right))
        x-is-pb = T.unit-is-equifibred $ x .right
      hom : Span-hom x (Span-id ⊗ x)
      hom .map = pb.universal $ x-is-pb .square
      hom .right = sym $ pullr pb.p₁∘universal ∙ idl _
      hom .left =
        x .left                                         ≡⟨ insertl T.μ-unitl ⟩
        T.μ _ ∘ T.η _ ∘ x .left                         ≡⟨ refl⟩∘⟨ T.unit.is-natural _ _ _ ⟩
        T.μ _ ∘ T.₁ (x .left) ∘ T.η (x .apex)          ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ pb.p₂∘universal ⟩
        T.μ _ ∘ T.₁ (x .left) ∘ pb.p₂ ∘ pb.universal _  ≡⟨ (refl⟩∘⟨ assoc _ _ _) ∙ assoc _ _ _ ⟩
        (T.μ _ ∘ T.₁ (x .left) ∘ pb.p₂) ∘ pb.universal _ ∎
    module sλ≅ {A B} (x : Span A B) = Spans._≅_ A B (sλ≅ x)

    sλ-natural : ∀ {A B} {x y : Span A B} (f : Span-hom x y)
              → (Span-hom-id {s = Span-id} ◆ f) .map ∘ (sλ≅.to x) .map
              ≡ (sλ≅.to y) .map C.∘ f .map
    sλ-natural {A} {B} {x} {y} f = Pullback.unique₂ (pb _ _)
        {p₁' = x .right} {p₂' = T.η _ ∘ f .map }
        {p = (refl⟩∘⟨ f .right) ∙ extendl (T.unit.is-natural (y .apex) _ (y .right))}
        (pulll pb.p₁∘universal ∙ (idl _ ⟩∘⟨refl) ∙ pb'.p₁∘universal)
        (pulll pb.p₂∘universal ∙ pullr pb''.p₂∘universal ∙ (sym $ T.unit.is-natural _ _ _ ))
        (pulll pb.p₁∘universal ∙ (sym $ f .right))
        (pulll pb.p₂∘universal) where
      module pb = Pullback (pb (T.η B) (T.₁ (y .right)))
      module pb' = Pullback (pb (left Span-id) (T.M₁ (x .right)))
      module pb'' = Pullback (pb (T.unit.η B) (T.M₁ (x .right)))
    sρ≅ : ∀ {A B} (x : Span A B) → Span-iso x (x ⊗ Span-id)
    sρ≅ {A} {B} x = mk-span-iso hom (pullback-unique' pb.has-is-pb x-is-pb) where
      module pb = Pullback (pb (x .left) (T.₁ id))
      abstract
        x-is-pb : is-pullback C id (x .left) (x .left) (T.₁ id)
        x-is-pb = transport (λ i → is-pullback C id (x .left) (x .left) (T.M-id (~ i)))
                            id-is-pullback

      hom : Span-hom x (x ⊗ Span-id)
      hom .map = pb.universal $ x-is-pb .square
      hom .left  =
        x .left                                         ≡˘⟨ (T.μ-unitr ⟩∘⟨refl) ∙ (idl _) ⟩
        (T.μ A ∘ T.₁ (T.η A)) ∘ x .left                 ≡⟨ refl⟩∘⟨ sym pb.p₂∘universal ⟩
        (T.μ A ∘ T.₁ (T.η A)) ∘ pb.p₂ ∘ pb.universal _  ≡⟨ assoc _ _ _ ∙ (sym (assoc _ _ _) ⟩∘⟨refl) ⟩
        (T.μ A ∘ T.₁ (T.η A) ∘ pb.p₂ ) ∘ pb.universal _ ∎
      hom .right = sym $ pullr pb.p₁∘universal ∙ idr _

    module sρ≅ {A B} (x : Span A B) = Spans._≅_ A B (sρ≅ x)

    sρ-natural : ∀ {A B} {x y : Span A B} (f : Span-hom x y)
              → (f ◆  Span-hom-id {s = Span-id}) .map C.∘ (sρ≅.to x) .map
              ≡ (sρ≅.to y) .map C.∘ f .map
    sρ-natural {A} {B} {x} {y} f = Pullback.unique₂ (pb _ _)
        {p₁' = f .map} {p₂' = x .left} {p = sym (f .left) ∙ introl T.M-id}
        (pulll pb.p₁∘universal ∙ cancelr pb'.p₁∘universal)
        (pulll pb.p₂∘universal ∙ (eliml T.M-id ⟩∘⟨refl) ∙ pb'.p₂∘universal)
        (cancell pb.p₁∘universal)
        (pulll pb.p₂∘universal ∙ (sym $ f .left)) where
      module pb = Pullback (pb (y .left) (T.₁ id))
      module pb' = Pullback (pb (left x) (T.M₁ id))

    sα≅ : ∀ {A B C D} (f : Span C D) (g : Span B C) (h : Span A B) → Span-iso  ((f ⊗ g) ⊗ h) (f ⊗ (g ⊗ h))
    sα≅ {A} {B} {C} {D} f g h = mk-span-iso {!  !} (pullback-unique' pb₁.has-is-pb {! !}) where
      module pbₗ = Pullback (pb (g .left) (T.₁ $ h .right))
      module pbₗ' = Pullback (pb (T.₁ $ g .left) (T.₁ $ T.₁ $ h .right))
      -- so we know (T pbₗ) ≅ pbₗ'
      module pb₁ = Pullback (pb (f .left) (T.₁ $ g .right ∘ pbₗ.p₁))
      _ : pb₁.apex ≡ (f ⊗ (g ⊗ h)) .apex
      _ = refl
      module pbᵣ = Pullback (pb (f .left) (T.₁ $ g .right))
      module pb₂ = Pullback (pb (T.μ B ∘ (T.₁ $ g .left) ∘ pbᵣ.p₂) (T.₁ $ h .right))
      _ : pb₂.apex ≡ ((f ⊗ g) ⊗ h) .apex
      _ = refl
      --??-is-pb : is-pullback C id (x .left) (x .left) (T.₁ id)

    module sα≅ {A B C D } (f : Span C D) (g : Span B C) (h : Span A B)  = Spans._≅_ A D (sα≅ f g h)

    module _ {A B C D} {f f' : Span C D}{g g' : Span B C} {h h' : Span A B}
                (α : Span-hom f f') (β : Span-hom g g') (γ : Span-hom h h') where
      sα-natural : (α ◆ (β ◆ γ)) .map ∘ (sα≅.to f g h) .map
                 ≡ (sα≅.to f' g' h') .map ∘ ((α ◆ β) ◆ γ) .map
      sα-natural = {! !}

  open make-natural-iso
  module Bicat = Prebicategory
  Spanᵇ : Prebicategory _ _ _
  Spanᵇ .Bicat.Ob = C.Ob
  Spanᵇ .Bicat.Hom = Spans
  Spanᵇ .Bicat.id = Span-id
  Spanᵇ .Bicat.compose = Span-∘
  Spanᵇ .Bicat.unitor-l = iso→isoⁿ sλ≅ λ f → Span-hom-path (sλ-natural f)
  Spanᵇ .Bicat.unitor-r = iso→isoⁿ sρ≅ λ f → Span-hom-path (sρ-natural f)
  Spanᵇ .Bicat.associator = iso→isoⁿ (λ (f , g , h) → sα≅ f g h) λ (f , g , h) → Span-hom-path (sα-natural f g h)
  Spanᵇ .Bicat.triangle f g = Span-hom-path $
    (sρ≅.from f ◀ g) .map ∘ sα≅.from f Span-id g .map ≡⟨ {! !} ⟩
    (f ▶ sλ≅.from g) .map  ∎
  Spanᵇ .Bicat.pentagon f g h i = {! !}
```

