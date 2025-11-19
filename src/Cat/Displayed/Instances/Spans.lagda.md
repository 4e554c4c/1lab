---
description: |
  Comma categories as two-sided displayed categories.
---
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
  where
private
  ℓc = o ⊔ ℓ
open import Cat.Bi.Instances.Spans C hiding (Spans)
```

# Spans as two-sided displayed categories


<!--
```agda


open Span
record Span-square {a b c d : Ob} (f : Hom a c) (g : Hom b d) (x : Span a b) (y : Span c d) : Type ℓc where
  no-eta-equality
  field
    map   : Hom (x .apex) (y .apex)
    left  : f ∘ x .left  ≡ y .left ∘ map
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
    (λ j → f j ∘ x .left) (λ j → s .left j) (λ j → s' .left j) (λ j → y .left ∘ p j) i j
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
    ; left = id-comm-sym
    ; right = id-comm-sym }
Spans ._∘'_ s s' = record 
    { map = s .map ∘ s' .map
    ; left = {! s .left !}
    ; right = {! !}
    }
Spans .idr' {a , b} {f , g} {s} {s'} h = Span-square-pathp (idr _)
Spans .idl' {a , b} {f , g} {s} {s'} h = Span-square-pathp (idl _)
Spans .hom[_] {f = f , g} {g = h , k} p s = record
    { map = s .map
    ; left  = (ap fst (sym p) ⟩∘⟨refl) ∙ s .left
    ; right = (ap snd (sym p) ⟩∘⟨refl) ∙ s .right
    }
Spans .coh[_] p s = Span-square-pathp refl
Spans .assoc' _ _ _ = Span-square-pathp (assoc _ _ _)

module DC = DoubleCategoryOver 
Spansᴰ : DoubleCategoryOver Spans
Spansᴰ .DC.e = span _ id id
Spansᴰ .DC.id[_] h = record 
  { map = h
  ; left = id-comm
  ; right = id-comm
  }
Spansᴰ .DC.id[]≡id = Span-square-pathp refl
Spansᴰ .DC.id[]∘ = Span-square-pathp refl
Spansᴰ .DC._⊚_ k v = span pb.apex (v .left ∘ p₂) (k .right ∘ p₁)
  where open module pb = Pullback (pb (k .left) (v .right))
Spansᴰ .DC._⊡_ {h₁ = h₁} {h₂} {k₁} {k₂} s₁ s₂ = record
  { map = pb2.universal {p₁' = s₁ .map ∘ pb1.p₁} {p₂' = s₂ .map ∘ pb1.p₂} {! !}
  ; left = {! !}
  ; right = {! !}
  }
  where 
    module pb1 = Pullback (pb (h₁ .left) (h₂ .right))
    module pb2 = Pullback (pb (k₁ .left) (k₂ .right))
Spansᴰ .DC.interchange α β γ δ = {! !}
Spansᴰ .DC.λ≅[_] h = record
  { to' = record
    { map = {! !}
    ; left = {! !}
    ; right = {! !} }
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
