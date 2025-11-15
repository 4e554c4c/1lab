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
open import Cat.Diagram.Monad.Solver
open import Cat.Bi.Base
open import Cat.Prelude hiding (⊤)
open import Cat.Functor.Bifunctor as Bi

import Cat.Reasoning
import Cat.Functor.Reasoning
```
-->

```agda
module Cat.Bi.Instances.T-Spans {o ℓ} {𝒞 : Precategory o ℓ} (T : CartesianMonad 𝒞) where

private
  open module 𝒞 = Cat.Reasoning 𝒞
  open module T = CartesianMonad T using () renaming (M₀ to T₀; M₁ to T₁)
  T² = T.M F∘ T.M
  open module T² = Functor T² using () renaming (F₀ to T²₀; F₁ to T²₁)

  underlying-Monad-on = T .CartesianMonad.U .snd


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

module _ (pb : has-pullbacks 𝒞) where
  open Functor
  open Pullbacks 𝒞 pb

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
          --open Pullback
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
    sλ≅ {A} {B} x = mk-span-iso hom (pullback-unique pb.has-is-pb x-is-pb) where
      module pb = Pullback (pb (T.η B) (T₁ (x .right)))
      abstract
        x-is-pb : is-pullback 𝒞 (x .right) (T.η B) (T.η (x .apex)) (T₁ (x .right))
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
    sρ≅ : ∀ {A B} (x : Span A B) → Span-iso x (x ⊗ Span-id)
    sρ≅ {A} {B} x = mk-span-iso hom (pullback-unique pb.has-is-pb x-is-pb) where
      module pb = Pullback (pb (x .left) (T₁ id))
      abstract
        x-is-pb : is-pullback 𝒞 id (x .left) (x .left) (T₁ id)
        x-is-pb = transport (λ i → is-pullback 𝒞 id (x .left) (x .left) (T.M-id (~ i)))
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

    abstract
      sλ-natural : ∀ {A B} {x y : Span A B} (f : Span-hom x y)
                → (Span-hom-id {s = Span-id} ◆ f) .map ∘ (sλ≅.to x) .map
                ≡ (sλ≅.to y) .map 𝒞.∘ f .map
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
      sρ-natural : ∀ {A B} {x y : Span A B} (f : Span-hom x y)
                → (f ◆  Span-hom-id {s = Span-id}) .map 𝒞.∘ (sρ≅.to x) .map
                ≡ (sρ≅.to y) .map 𝒞.∘ f .map
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
	{T(Th\times_{TC}g)} & Tg & {Tg\times_{TB}f}
	\arrow[from=1-1, to=1-2]
	\arrow[from=1-3, to=1-2]
\end{tikzcd}\]
~~~
witnessing isomorphism.

```agda

    sα≅ : ∀ {A B C D} (f : Span C D) (g : Span B C) (h : Span A B) → Span-iso  ((f ⊗ g) ⊗ h) (f ⊗ (g ⊗ h))
    sα≅ {A} {B} {C} {D} f g h = mk-span-iso hom (pullback-unique pb₁-is-pb-inner pb₂-is-pb-inner) module sα≃-data where
      module f = Span f
      module g = Span g
      module h = Span h
      module g⊗h   = Pullback (pb g.left (T₁  h.right))
      g⊗h = g⊗h.apex
      module f⊗g = Pullback (pb (f.left) (T₁ g.right))
      f⊗g = f⊗g.apex
      module pb₁ = Pullback (pb f.left (T₁ $ g.right ∘ g⊗h.p₁))
      module pb₂ = Pullback (pb (T.μ B ∘ T₁ g.left ∘ f⊗g.p₂) (T₁ h.right))
      pb₁ = pb₁.apex
      pb₂ = pb₂.apex

      _ : pb₁ ≡ (f ⊗ (g ⊗ h)) .apex
      _ = refl
      _ : pb₂ ≡ ((f ⊗ g) ⊗ h) .apex
      _ = refl

      -- first, the "easy" direction. We need a unique arrow pb₁ -> (f ⊗ g)
      !₀ : Hom pb₁ f⊗g
      !₀ = f⊗g.universal {p₁' = pb₁.p₁} {p₂' = T₁ g⊗h.p₁ ∘ pb₁.p₂} (pb₁.square ∙ pushl (T.M-∘ _ _))

      -- which makes the outer square into a pullback
      opaque
        pb₁-is-pb-outer : is-pullback 𝒞 (f⊗g.p₁ ∘ !₀) f.left pb₁.p₂ (T₁ g.right ∘ T₁ g⊗h.p₁)
        pb₁-is-pb-outer = transport (λ i → is-pullback 𝒞 (p i) f.left pb₁.p₂ (T.M-∘ g.right g⊗h.p₁ i)) pb₁.has-is-pb
          where p : pb₁.p₁ ≡ (f⊗g.p₁ ∘ !₀)
                p = sym $ f⊗g.p₁∘universal {p₁' = pb₁.p₁} {p₂' = T₁ g⊗h.p₁ ∘ pb₁.p₂}

        -- now we need to make a similar "outer" square for pb₂. This is is more complicated, however,
        -- since we don't have a single pullback square to paste under pb₂. Instead, we have two:
        --  * one formed by the image of g⊗h's square under T, and
        --  * another formed by the equifibred nature of μ.

        T[g⊗h]-is-pb : is-pullback 𝒞  (T₁ g⊗h.p₁) (T₁ g.left) (T₁ g⊗h.p₂) (T²₁ h.right)
        T[g⊗h]-is-pb = T.pres-pullback g⊗h.has-is-pb

        μ-is-pb : is-pullback 𝒞  (T²₁ h.right) (T.μ B) (T.μ h.apex) (T₁ h.right)
        μ-is-pb = T.mult-is-equifibred h.right

        -- now we can paste these together into a single square
        T[g⊗h]-is-pasted-pb : is-pullback 𝒞 (T₁ g⊗h.p₁) (T.μ B ∘ T₁ g.left) (T.μ h.apex ∘ T₁ g⊗h.p₂) (T₁ h.right)
        -- we need to rotate our squares bc we're currently working top-down instead of left-right
        T[g⊗h]-is-pasted-pb = rotate-pullback $ pasting-left→outer-is-pullback (rotate-pullback μ-is-pb) (rotate-pullback T[g⊗h]-is-pb)
      module T[g⊗h]-is-pasted-pb = is-pullback T[g⊗h]-is-pasted-pb
      module T[g⊗h]-is-pb = is-pullback T[g⊗h]-is-pb

      -- now we need a unique arrow pb₂ -> T[g⊗h]
      !₁ : Hom pb₂ (T₀ g⊗h)
      !₁ = T[g⊗h]-is-pasted-pb .universal {p₁' = f⊗g.p₂ ∘ pb₂.p₁} {p₂' = pb₂.p₂} $
        (T.μ B ∘ T₁ g.left) ∘ f⊗g.p₂ ∘ pb₂.p₁ ≡⟨ cat! 𝒞 ⟩
        (T.μ B ∘ T₁ g.left ∘ f⊗g.p₂) ∘ pb₂.p₁ ≡⟨ pb₂.square ⟩
        T₁ h.right ∘ pb₂.p₂                   ∎

      -- which turns pb₂ into a pullback of the larger square
      abstract
        pb₂-is-pb-outer : is-pullback 𝒞 pb₂.p₁ ((T.μ B ∘ T₁ g.left) ∘ f⊗g.p₂) ((T.μ h.apex ∘ T₁ g⊗h.p₂) ∘ !₁) (T₁ h.right)
        pb₂-is-pb-outer = transport (λ i → is-pullback 𝒞 pb₂.p₁ (pₗ i) (pᵣ i) (T₁ h.right)) pb₂.has-is-pb
          where pₗ : T.μ B ∘ T₁ g.left ∘ f⊗g.p₂ ≡ (T.μ B ∘ T₁ g.left) ∘ f⊗g.p₂
                pₗ = cat! 𝒞
                pᵣ : pb₂.p₂ ≡ (T.μ h.apex ∘ T₁ g⊗h.p₂) ∘ !₁
                pᵣ = sym $ T[g⊗h]-is-pasted-pb .p₂∘universal

        -- so basically what we're aiming for is
        pb₁-is-pb-inner : is-pullback 𝒞 !₀ f⊗g.p₂ pb₁.p₂  (T₁ g⊗h.p₁)
        pb₁-is-pb-inner = pasting-outer→left-is-pullback f⊗g.has-is-pb pb₁-is-pb-outer f⊗g.p₂∘universal
        module pb₁-is-pb-inner = is-pullback pb₁-is-pb-inner

        pb₂-is-pb-inner : is-pullback 𝒞 pb₂.p₁ f⊗g.p₂ !₁ (T₁ g⊗h.p₁)
        pb₂-is-pb-inner = rotate-pullback $ pasting-outer→left-is-pullback (rotate-pullback T[g⊗h]-is-pasted-pb) (rotate-pullback pb₂-is-pb-outer) T[g⊗h]-is-pasted-pb.p₁∘universal
        module pb₂-is-pb-inner = is-pullback pb₂-is-pb-inner

      -- now we may form our universal span morphism
      hom : Span-hom ((f ⊗ g) ⊗ h) (f ⊗ (g ⊗ h))
      hom .map = pb₁-is-pb-inner .universal $ pb₂-is-pb-inner .square
      hom .right =
        ((f ⊗ g) ⊗ h) .right              ≡˘⟨ assoc _ _ _ ⟩
        f .right ∘ f⊗g.p₁ ∘ pb₂.p₁        ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ pb₁-is-pb-inner .p₁∘universal {p = pb₂-is-pb-inner .square} ⟩
        f .right ∘ f⊗g.p₁ ∘ !₀ ∘ hom .map ≡⟨ refl⟩∘⟨ pulll f⊗g.p₁∘universal ⟩
        f .right ∘ pb₁.p₁ ∘ hom .map      ≡⟨ assoc _ _ _ ⟩
        (f ⊗ g ⊗ h) .right ∘ hom .map     ∎
      hom .left =
        ((f ⊗ g) ⊗ h) .left              ≡⟨⟩
        T.μ A ∘ T₁ h.left ∘ pb₂.p₂       ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ T[g⊗h]-is-pasted-pb .p₂∘universal ⟩
        T.μ A ∘ T₁ h.left ∘ (T.μ _ ∘ T₁ g⊗h.p₂) ∘ !₁
                                         ≡⟨ monad! underlying-Monad-on ⟩
        T.μ A ∘ T₁ (T.μ A ∘ T₁ h.left ∘ g⊗h.p₂) ∘ !₁
                                         ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ pb₁-is-pb-inner .p₂∘universal {p = pb₂-is-pb-inner .square} ⟩
        T.μ A ∘ T₁ (T.μ A ∘ T₁ h.left ∘ g⊗h.p₂) ∘ pb₁.p₂ ∘ hom .map
                                         ≡⟨ pulll3 refl ⟩
        (T.μ A ∘ T₁ (T.μ A ∘ T₁ h.left ∘ g⊗h.p₂) ∘ pb₁.p₂) ∘ hom .map
                                         ≡⟨⟩
        (f ⊗ g ⊗ h) .left ∘ hom .map     ∎

    module sα≅ {A B C D } (f : Span C D) (g : Span B C) (h : Span A B)  = Spans._≅_ A D (sα≅ f g h)
    module _ {A B C} {f f' : Span B C} {g g' : Span A B} (α : Span-hom f f') (β : Span-hom g g') where
      private
          module f = Span f
          module g = Span g
          module f⊗g = Pullback (pb (f.left) (T₁ g.right))
          module f' = Span f'
          module g' = Span g'
          module f'⊗g' = Pullback (pb (f'.left) (T₁ g'.right))
      lemmaaaaa =
        α .map ∘ f⊗g.p₁ ≡˘⟨ f'⊗g'.p₁∘universal ⟩
        f'⊗g'.p₁ ∘ (α ◆ β) .map ∎

    module _ {A B C D} {f f' : Span C D}{g g' : Span B C} {h h' : Span A B}
                (α : Span-hom f f') (β : Span-hom g g') (γ : Span-hom h h') where abstract
      private
        module f⊗g⊗h-assoc = sα≃-data f g h
        module f'⊗g'⊗h'-assoc = sα≃-data f' g' h'
        module f = Span f
        module g = Span g
        module h = Span h
        module f' = Span f'
        module g' = Span g'
        module h' = Span h'
        module f⊗g = Pullback (pb (f.left) (T₁ g.right))
        module g⊗h   = Pullback (pb g.left (T₁  h.right))
        module f'⊗g' = Pullback (pb (f'.left) (T₁ g'.right))
        module g'⊗h'   = Pullback (pb g'.left (T₁  h'.right))
      sα-natural : (α ◆ (β ◆ γ)) .map ∘ (sα≅.to f g h) .map
                 ≡ (sα≅.to f' g' h') .map ∘ ((α ◆ β) ◆ γ) .map
      sα-natural = f'⊗g'⊗h'-assoc.pb₁-is-pb-inner.unique₂
        {p₁' = (α ◆ β) .map ∘ f⊗g⊗h-assoc.pb₂.p₁} {p₂' = (T₁ $ (β ◆ γ) .map) ∘ f⊗g⊗h-assoc.!₁}
        {p = f'⊗g'.p₂  ∘ (α ◆ β) .map ∘ f⊗g⊗h-assoc.pb₂.p₁    ≡⟨ {! !} ⟩
             T₁ (β .map) ∘ f⊗g.p₂ ∘ f⊗g⊗h-assoc.pb₂.p₁        ≡⟨ {! !} ⟩
             T₁ (β .map) ∘ T₁ g⊗h.p₁ ∘ f⊗g⊗h-assoc.!₁         ≡⟨ {! !} ⟩
             T₁ (β .map ∘ g⊗h.p₁) ∘ f⊗g⊗h-assoc.!₁            ≡⟨ {! !} ⟩
             T₁ (g'⊗h'.p₁ ∘ (β ◆ γ) .map) ∘ f⊗g⊗h-assoc.!₁    ≡⟨ {! !} ⟩
             T₁ g'⊗h'.p₁ ∘ T₁ ((β ◆ γ) .map) ∘ f⊗g⊗h-assoc.!₁ ≡⟨ {! !} ⟩
             T₁ g'⊗h'.p₁ ∘ T₁ ((β ◆ γ) .map) ∘ f⊗g⊗h-assoc.!₁ ∎}
        (
          f'⊗g'⊗h'-assoc.!₀ ∘ (α ◆ β ◆ γ) .map ∘ sα≅.to f g h .map ≡⟨ {! !} ⟩
          f'⊗g'⊗h'-assoc.!₀ ∘ (sα≅.to f' g' h') .map ∘ ((α ◆ β) ◆ γ) .map ≡⟨ {! !} ⟩
          (α ◆ β) .map ∘ f⊗g⊗h-assoc.!₀ ∘ (sα≅.to f g h) .map        ≡⟨ {! !} ⟩
          (α ◆ β) .map ∘ f⊗g⊗h-assoc.pb₂.p₁                          ∎
        )
        (
          f'⊗g'⊗h'-assoc.pb₁.p₂ ∘ (α ◆ β ◆ γ) .map ∘ sα≅.to f g h .map ≡⟨ ? ⟩
          T₁ ((β ◆ γ) .map) ∘ f⊗g⊗h-assoc.!₁ ∎
        )
        {! !}
        {! !}

  open make-natural-iso
  module Bicat = Prebicategory
  Spanᵇ : Prebicategory _ _ _
  Spanᵇ .Bicat.Ob = 𝒞.Ob
  Spanᵇ .Bicat.Hom = Spans
  Spanᵇ .Bicat.id = Span-id
  Spanᵇ .Bicat.compose = Span-∘
  Spanᵇ .Bicat.unitor-l = iso→isoⁿ sλ≅ λ f → Span-hom-path (sλ-natural f)
  Spanᵇ .Bicat.unitor-r = iso→isoⁿ sρ≅ λ f → Span-hom-path (sρ-natural f)
  Spanᵇ .Bicat.associator = iso→isoⁿ (λ (f , g , h) → sα≅ f g h) λ (f , g , h) → Span-hom-path (sα-natural f g h)
  Spanᵇ .Bicat.triangle f g = Span-hom-path $ {! !}
  Spanᵇ .Bicat.pentagon f g h i = {! !}
```
