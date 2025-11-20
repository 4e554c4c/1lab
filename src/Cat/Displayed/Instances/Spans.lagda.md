<!--
```agda
open import Cat.Displayed.TwoSided.Discrete
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Double
open import Cat.Instances.Product
open import Cat.Displayed.Base
open import Cat.Prelude
open import Cat.Diagram.Pullback
open import Cat.Diagram.Monad.Pullback

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->
```agda
module Cat.Displayed.Instances.Spans
  {o ℓ}
  {C : Precategory o ℓ}
  (let open module C = Cat.Reasoning C)
  (pb : ∀ {a b c} (f : Hom a b) (g : Hom c b) → Pullback C f g)
  (T : CartesianMonad C)
  where
private
  ℓc = o ⊔ ℓ
```

# Spans as two-sided displayed categories


```agda

private
  open module T = CartesianMonad T using () renaming (M₀ to T₀; M₁ to T₁)
  T² = T.M F∘ T.M
  open module T² = Functor T² using () renaming (F₀ to T²₀; F₁ to T²₁)

  underlying-Monad-on = T .CartesianMonad.U .snd


record Span (a b : Ob) : Type (o ⊔ ℓ) where
  constructor t-span
  field
    apex  : Ob
    left  : Hom apex (T₀ a)
    right : Hom apex b

module span-∘ {a b c} (s : Span b c) (t : Span a b) where
  open Pullback (pb (s .Span.left) (T₁ (t .Span.right))) public
  module dst = Span s
  module src = Span t
  left = T.μ _ ∘ T₁ src.left ∘ p₂
  right = dst.right ∘ p₁

span-∘ : ∀ {a b c} (s : Span b c) (t : Span a b) → Span a c
span-∘ s t = record { span-∘ s t }

open Span

record Span-square {a b c d : Ob} (f : Hom a c) (g : Hom b d) (x : Span a b) (y : Span c d) : Type ℓc where
  no-eta-equality
  field
    map   : Hom (x .apex) (y .apex)
    left  : (T₁ f) ∘ x .left  ≡ y .left ∘ map
    right : g ∘ x .right ≡ y .right ∘ map
open Span-square

unquoteDecl H-Level-Span-square = declare-record-hlevel 2 H-Level-Span-square (quote Span-square)

Span-square-pathp
  : {a b c d : Ob}
    {f : I → Hom a c}
    {g : I → Hom b d}
    {x : Span a b}
    {y : Span c d}
    {s : Span-square (f i0) (g i0) x y}
    {s' : Span-square (f i1) (g i1) x y}
  → s .map ≡ s' .map
  → PathP (λ i → Span-square (f i) (g i) x y) s s'
Span-square-pathp p i .map = p i
Span-square-pathp  {f = f} {g = g} {x = x} {y} {s} {s'} p i .left j =
  is-set→squarep (λ i j → Hom-set _ _)
    (λ j → T₁ (f j) ∘ x .left) (λ j → s .left j) (λ j → s' .left j) (λ j → y .left ∘ p j) i j
Span-square-pathp  {f = f} {g = g} {x = x} {y} {s} {s'} p i .right j =
  is-set→squarep (λ i j → Hom-set _ _)
    (λ j → g j ∘ x .right) (λ j → s .right j) (λ j → s' .right j) (λ j → y .right ∘ p j) i j

open Displayed
Spans : Displayed (C ×ᶜ C) ℓc ℓc
Spans .Ob[_] (a , b) = Span a b
Spans .Hom[_] (f , g) = Span-square f g
Spans .Hom[_]-set (f , g) h w = hlevel 2
Spans .id' {a , b} = record
    { map = id
    ; left = T.eliml refl ∙ sym (idr _)
    ; right = id-comm-sym }
Spans ._∘'_ s s' = record
    { map = s .map ∘ s' .map
    ; left = T.popr (s' .left) ∙ extendl (s .left)
    ; right = pullr (s' .right) ∙ extendl (s .right)
    }
Spans .idr' _ = Span-square-pathp (idr _)
Spans .idl' _ = Span-square-pathp (idl _)
Spans .hom[_] {f = f , g} {g = h , k} p s = record
    { map = s .map
    ; left  = (ap (T₁ ⊙ fst) (sym p) ⟩∘⟨refl)  ∙ s .left
    ; right = (ap snd (sym p) ⟩∘⟨refl) ∙ s .right
    }
Spans .coh[_] p s = Span-square-pathp refl
Spans .assoc' _ _ _ = Span-square-pathp (assoc _ _ _)

module DC = DoubleCategoryOver
Spansᴰ : DoubleCategoryOver Spans
Spansᴰ .DC.e {a} = t-span a (T.η a) id
Spansᴰ .DC.id[_] h = record
  { map = h
  ; left = sym $ T.unit.is-natural _ _ _
  ; right = id-comm
  }
Spansᴰ .DC.id[]≡id = Span-square-pathp refl
Spansᴰ .DC.id[]∘ = Span-square-pathp refl
Spansᴰ .DC._⊚_ = span-∘
Spansᴰ .DC._⊡_ {h₁ = s} {t} {s'} {t'} σ τ = record
  { map = s'∘t'.universal {p₁' = σ.map ∘ s∘t.p₁} {p₂' = T₁ τ.map ∘ s∘t.p₂} comm
  ; left = {! !}
  ; right = {! !}
  }
  where
    module s∘t = span-∘ s t
    module s'∘t' = span-∘ s' t'
    module s' = Span s'
    module t' = Span t'
    module σ = Span-square σ
    module τ = Span-square τ
    comm =
      s'.left ∘ σ.map ∘ s∘t.p₁ ≡⟨ extendl (sym σ.left) ⟩
      T₁ _ ∘ s∘t.dst.left ∘ s∘t.p₁ ≡⟨ refl⟩∘⟨ s∘t.square ⟩
      T₁ _ ∘ T₁ s∘t.src.right ∘ s∘t.p₂ ≡⟨ extendl (T.weave τ.right) ⟩
      T₁ t'.right ∘ T₁ τ.map ∘ s∘t.p₂ ∎
Spansᴰ .DC.interchange α β γ δ = {! !}
Spansᴰ .DC.λ≅[_] h = record
  { to' = {! !}
  ; from' = {! !}
  ; inverses' = {! !} }
Spansᴰ .DC.ρ≅[_] h = {! !}
Spansᴰ .DC.κ≅[_,_,_] f g h = {! !}
Spansᴰ .DC.λ-nat α = {! !}
Spansᴰ .DC.ρ-nat α = {! !}
Spansᴰ .DC.κ-nat α β γ = {! !}
Spansᴰ .DC.triangle = {! !}
Spansᴰ .DC.pentagon = {! !}
```
