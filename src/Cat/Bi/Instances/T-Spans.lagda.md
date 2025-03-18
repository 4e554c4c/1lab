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
  open module T = CartesianMonad T using () renaming (M₀ to T₀; M₁ to T₁)
  T² = T.M F∘ T.M
  open module T² = Functor T² using () renaming (F₀ to T²₀; F₁ to T²₁)
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
  Span-∘ .F₀ (sp1 , sp2) = t-span pb.apex (T.μ _ ∘ T₁ (sp2 .left) ∘ pb.p₂) (sp1 .right ∘ pb.p₁)
     where module pb = Pullback (pb (sp1 .left) (T₁ (sp2 .right)))
  Span-∘ .F₁ {x1 , x2} {y1 , y2} (f , g) = res
    where
      module x = Pullback (pb (x1 .left) (T₁ (x2 .right)))
      module y = Pullback (pb (y1 .left) (T₁ (y2 .right)))
      x→y : Hom x.apex y.apex
      x→y = y.universal {p₁' = f .map ∘ x.p₁} {p₂' = T₁ (g .map) ∘ x.p₂} comm
        where abstract
          open Pullback
          comm : y1 .left ∘ f .map ∘ x.p₁ ≡ T₁ (y2 .right) ∘ T₁ (g .map) ∘ x.p₂
          comm = pulll (sym (f .left)) ∙ x.square ∙ (pushl $ T.expand $ g .right)
      res : Span-hom (Span-∘ .F₀ (x1 , x2))  (Span-∘ .F₀ (y1 , y2))
      res .map = x→y
      res .left = T.μ _ ∘ T₁ (x2 .left) ∘ x.p₂                     ≡⟨ refl⟩∘⟨ pushl (T.expand (g .left)) ⟩
                  T.μ _ ∘ T₁ (y2 .left) ∘ T₁ (g .map) ∘ x.p₂     ≡˘⟨ refl⟩∘⟨ pullr y.p₂∘universal  ⟩
                  T.μ _ ∘ (T₁ (y2 .left) ∘ pb.p₂) ∘ pb.universal _ ≡⟨ assoc _ _ _  ⟩
                  (T.μ _ ∘ T₁ (y2 .left) ∘ pb.p₂) ∘ pb.universal _ ∎
        where module pb = Pullback (pb (y1 .left) (T₁ (y2 .right)))
      res .right = sym (pullr y.p₁∘universal ∙ pulll (sym (f .right)))

  Span-∘ .F-id {x1 , x2} = Span-hom-path $ sym $ x.unique id-comm (idr x.p₂ ∙ (sym $ eliml T.M-id))
    where module x = Pullback (pb (x1 .left) (T₁ (x2 .right)))

  Span-∘ .F-∘ {x1 , x2} {y1 , y2} {z1 , z2} f g =
    Span-hom-path $ sym $ z.unique
      (pulll z.p₁∘universal ∙ pullr y.p₁∘universal ∙ assoc _ _ _)
      (pulll z.p₂∘universal ∙ pullr y.p₂∘universal ∙ assoc _ _ _ ∙ (sym $ T.M-∘ _ _ ⟩∘⟨refl))
    where
      module x = Pullback (pb (x1 .left) (T₁ (x2 .right)))
      module y = Pullback (pb (y1 .left) (T₁ (y2 .right)))
      module z = Pullback (pb (z1 .left) (T₁ (z2 .right)))

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

Both unitors are relatively straightforward by noticing that, as $\eta$
is Cartesian, both $f$ and $\id_B\circ f$ (defined as $Tf\times_{TB} B$)
are pullbacks of the same square.

~~~{.quiver}
\[\begin{tikzcd}
	f \\
	& {Tf\times_{TB}B} & B \\
	& Tf & TB
	\arrow["\ell", curve={height=-18pt}, from=1-1, to=2-3]
	\arrow["{\eta_f}"', curve={height=18pt}, from=1-1, to=3-2]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
	\arrow["{{\pi_2}}", from=2-2, to=2-3]
	\arrow["{{\pi_1}}"', from=2-2, to=3-2]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=2-2, to=3-3]
	\arrow["{\eta_B}"', from=2-3, to=3-3]
	\arrow["{T\ell}", from=3-2, to=3-3]
\end{tikzcd}\]
~~~

```agda
    sλ≅ : ∀ {A B} (x : Span A B) → Span-iso x (Span-id ⊗ x)
    sλ≅ {A} {B} x = mk-span-iso hom (pullback-unique' pb.has-is-pb x-is-pb) where
      module pb = Pullback (pb (T.η B) (T₁ (x .right)))
      abstract
        x-is-pb : is-pullback C (x .right) (T.η B) (T.η (x .apex)) (T₁ (x .right))
        x-is-pb = T.unit-is-equifibred $ x .right
      hom : Span-hom x (Span-id ⊗ x)
      hom .map = pb.universal $ x-is-pb .square
      hom .right = sym $ pullr pb.p₁∘universal ∙ idl _
      hom .left =
        x .left                                         ≡⟨ insertl T.μ-unitl ⟩
        T.μ _ ∘ T.η _ ∘ x .left                         ≡⟨ refl⟩∘⟨ T.unit.is-natural _ _ _ ⟩
        T.μ _ ∘ T₁ (x .left) ∘ T.η (x .apex)          ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ pb.p₂∘universal ⟩
        T.μ _ ∘ T₁ (x .left) ∘ pb.p₂ ∘ pb.universal _  ≡⟨ (refl⟩∘⟨ assoc _ _ _) ∙ assoc _ _ _ ⟩
        (T.μ _ ∘ T₁ (x .left) ∘ pb.p₂) ∘ pb.universal _ ∎
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
      module pb = Pullback (pb (T.η B) (T₁ (y .right)))
      module pb' = Pullback (pb (left Span-id) (T₁ (x .right)))
      module pb'' = Pullback (pb (T.unit.η B) (T₁ (x .right)))
    sρ≅ : ∀ {A B} (x : Span A B) → Span-iso x (x ⊗ Span-id)
    sρ≅ {A} {B} x = mk-span-iso hom (pullback-unique' pb.has-is-pb x-is-pb) where
      module pb = Pullback (pb (x .left) (T₁ id))
      abstract
        x-is-pb : is-pullback C id (x .left) (x .left) (T₁ id)
        x-is-pb = transport (λ i → is-pullback C id (x .left) (x .left) (T.M-id (~ i)))
                            id-is-pullback

      hom : Span-hom x (x ⊗ Span-id)
      hom .map = pb.universal $ x-is-pb .square
      hom .left  =
        x .left                                         ≡˘⟨ (T.μ-unitr ⟩∘⟨refl) ∙ (idl _) ⟩
        (T.μ A ∘ T₁ (T.η A)) ∘ x .left                 ≡⟨ refl⟩∘⟨ sym pb.p₂∘universal ⟩
        (T.μ A ∘ T₁ (T.η A)) ∘ pb.p₂ ∘ pb.universal _  ≡⟨ assoc _ _ _ ∙ (sym (assoc _ _ _) ⟩∘⟨refl) ⟩
        (T.μ A ∘ T₁ (T.η A) ∘ pb.p₂ ) ∘ pb.universal _ ∎
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
      module pb = Pullback (pb (y .left) (T₁ id))
      module pb' = Pullback (pb (left x) (T₁ id))

```

Proving associativity is a bit more complicated. We need the [[pasting
law for pullbacks]], that $\mu$ is a [[Cartesian natural transformation]]
and that $T$ is a [[Cartesian functor]].

The diagram, after adding a Cartesian square for $\mu$ is

~~~{.quiver}
\[\begin{tikzcd}
	& {T(Th\times_{TC}g)\times_{TB}f} \\
	{Th\times_{TC}(Tg\times_{TB}f)} && {Tg\times_{TB}f} & f \\
	& {T(Th\times_{TC}g)} & Tg & TB \\
	& {T^2h} & {T^2C} \\
	& Th & TC.
	\arrow[dotted, from=1-2, to=2-4]
	\arrow[dotted, from=1-2, to=3-2]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-2, to=3-4]
	\arrow[dotted, from=2-1, to=2-3]
	\arrow[dotted, from=2-1, to=5-2]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=2-1, to=5-3]
	\arrow[from=2-3, to=2-4]
	\arrow[from=2-3, to=3-3]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=2-3, to=3-4]
	\arrow["{\ell_f}", from=2-4, to=3-4]
	\arrow[from=3-2, to=3-3]
	\arrow[from=3-2, to=4-2]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=3-2, to=4-3]
	\arrow["{T(\ell_g)}", from=3-3, to=3-4]
	\arrow["{T(r_g)}", from=3-3, to=4-3]
	\arrow["{T^2(\ell_h)}", from=4-2, to=4-3]
	\arrow["\mu", from=4-2, to=5-2]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=4-2, to=5-3]
	\arrow["\mu", from=4-3, to=5-3]
	\arrow["{T(\ell_h)}", from=5-2, to=5-3]
\end{tikzcd}\]
~~~

By uniqueness of pullbacks, we may prove that both
$f\circ(g\circ h)$ and $(f\circ g)\circ h$ are pullbacks of the central cospan
~~~{.quiver}
\[\begin{tikzcd}
	{} \\
	{T(Th\times_{TC}g)} & Tg & {Tg\times_{TB}f}
	\arrow[from=2-1, to=2-2]
	\arrow[from=2-3, to=2-2]
\end{tikzcd}\]
~~~
witnessing isomorphism.

```agda

    sα≅ : ∀ {A B C D} (f : Span C D) (g : Span B C) (h : Span A B) → Span-iso  ((f ⊗ g) ⊗ h) (f ⊗ (g ⊗ h))
    sα≅ {A} {B} {D} f g h = mk-span-iso hom (pullback-unique' c₁-is-pb c₂-is-pb) where
      module f = Span f
      module g = Span g
      module h = Span h
      module pb₀ = Pullback (pb g.left (T₁  h.right))
      pb₀ = pb₀.apex
      module pbᵣ = Pullback (pb (f.left) (T₁ g.right))
      pbᵣ = pbᵣ.apex
      module c₁ = Pullback (pb f.left (T₁ $ g.right ∘ pb₀.p₁))
      module c₂ = Pullback (pb (T.μ B ∘ T₁ g.left ∘ pbᵣ.p₂) (T₁ h.right))
      c₁ = c₁.apex
      c₂ = c₂.apex

      _ : c₁ ≡ (f ⊗ (g ⊗ h)) .apex
      _ = refl
      _ : c₂ ≡ ((f ⊗ g) ⊗ h) .apex
      _ = refl


      -- first, the "easy" direction. We need a unique arrow c₁ -> (f ⊗ g)
      !₀ : Hom c₁ pbᵣ
      !₀ = pbᵣ.universal {p₁' = c₁.p₁} {p₂' = T₁ pb₀.p₁ ∘ c₁.p₂} (c₁.square ∙ pushl (T.M-∘ _ _))

      -- which makes the outer square into a pullback
      abstract
        c₁-is-pb-outer : is-pullback C (pbᵣ.p₁ ∘ !₀) f.left c₁.p₂ (T₁ g.right ∘ T₁ pb₀.p₁)
        c₁-is-pb-outer = transport (λ i → is-pullback C (p i) f.left c₁.p₂ (T.M-∘ g.right pb₀.p₁ i)) c₁.has-is-pb
          where p : c₁.p₁ ≡ (pbᵣ.p₁ ∘ !₀)
                p = sym $ pbᵣ.p₁∘universal {p₁' = c₁.p₁} {p₂' = T₁ pb₀.p₁ ∘ c₁.p₂}

        -- now we need to make a similar "outer" square for c₂. This is is more complicated, however,
        -- since we don't have a single pullback square to paste under c₂. Instead, we have two:
        --  * one formed by the image of pb₀'s square under T, and
        --  * another formed by the equifibred nature of μ.

        T[pb₀]-is-pb : is-pullback C  (T₁ pb₀.p₁) (T₁ g.left) (T₁ pb₀.p₂) (T²₁ h.right)
        T[pb₀]-is-pb = T.pres-pullback pb₀.has-is-pb

        μ-is-pb : is-pullback C  (T²₁ h.right) (T.μ B) (T.μ h.apex) (T₁ h.right)
        μ-is-pb = T.mult-is-equifibred h.right

        -- now we can paste these together into a single square
        T[pb₀]-is-pasted-pb : is-pullback C (T₁ pb₀.p₁) (T.μ B ∘ T₁ g.left) (T.μ h.apex ∘ T₁ pb₀.p₂) (T₁ h.right)
        -- we need to rotate our squares bc we're currently working top-down instead of left-right
        T[pb₀]-is-pasted-pb = rotate-pullback $ pasting-left→outer-is-pullback (rotate-pullback μ-is-pb) (rotate-pullback T[pb₀]-is-pb)

      -- now we need a unique arrow c₂ -> T[pb₀]
      !₁ : Hom c₂ (T₀ pb₀)
      !₁ = T[pb₀]-is-pasted-pb .universal {p₁' = pbᵣ.p₂ ∘ c₂.p₁} {p₂' = c₂.p₂} $
        (T.μ B ∘ T₁ g.left) ∘ pbᵣ.p₂ ∘ c₂.p₁ ≡⟨ cat! C ⟩
        (T.μ B ∘ T₁ g.left ∘ pbᵣ.p₂) ∘ c₂.p₁ ≡⟨ c₂.square ⟩
        T₁ h.right ∘ c₂.p₂                   ∎

      -- which turns c₂ into a pullback of the larger square
      abstract
        c₂-is-pb-outer : is-pullback C c₂.p₁ ((T.μ B ∘ T₁ g.left) ∘ pbᵣ.p₂) ((T.μ h.apex ∘ T₁ pb₀.p₂) ∘ !₁) (T₁ h.right)
        c₂-is-pb-outer = transport (λ i → is-pullback C c₂.p₁ (pₗ i) (pᵣ i) (T₁ h.right)) c₂.has-is-pb
          where pₗ : T.μ B ∘ T₁ g.left ∘ pbᵣ.p₂ ≡ (T.μ B ∘ T₁ g.left) ∘ pbᵣ.p₂
                pₗ = cat! C
                pᵣ : c₂.p₂ ≡ (T.μ h.apex ∘ T₁ pb₀.p₂) ∘ !₁
                pᵣ = sym $ T[pb₀]-is-pasted-pb .p₂∘universal

        -- so basically what we're aiming for is
        c₁-is-pb : is-pullback C !₀ pbᵣ.p₂ c₁.p₂  (T₁ pb₀.p₁)
        c₁-is-pb = pasting-outer→left-is-pullback pbᵣ.has-is-pb c₁-is-pb-outer {! !}

        c₂-is-pb : is-pullback C c₂.p₁ pbᵣ.p₂ !₁ (T₁ pb₀.p₁)
        c₂-is-pb = rotate-pullback $ pasting-outer→left-is-pullback (rotate-pullback T[pb₀]-is-pasted-pb) (rotate-pullback c₂-is-pb-outer) {! !}

      -- now we may form our universal span morphism
      hom : Span-hom ((f ⊗ g) ⊗ h) (f ⊗ (g ⊗ h))
      hom .map = c₁-is-pb .universal $ c₂-is-pb .square
      hom .right = {! !}
      hom .left = {! !}
      --??-is-pb : is-pullback C id (x .left) (x .left) (T₁ id)

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
    (sρ≅.from f ◀ g) .map ∘ sα≅.from f Span-id g .map ≡⟨
      Pullback.unique₂ (pb _ _) {p₁' = pb _ _ .p₁} {p₂' = (T.μ _ ∘ T₁ (pb _ _ .p₂)) ∘ pb _ _ .p₂} {p = {! !}}
        {! !} {! !} {! !} {! !}
      ⟩
    (f ▶ sλ≅.from g) .map  ∎
  Spanᵇ .Bicat.pentagon f g h i = {! !}
```

