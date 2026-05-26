<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Displayed.Functor
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Functor.Closed
open import Cat.Functor.Base
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as Disp
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Bi.Instances.Displayed {o ℓ} (B : Precategory o ℓ) (o' ℓ' : Level) where
open Prebicategory
```

<!--
```agda
private variable
  o'' ℓ'' : Level
```
-->

# The bicategory of displayed categories over a base

Since [[displayed categories]] provide a natural setting for "relative
category theory", i.e. the study of categories *relative to a base*, we
should expect that the collection of displayed categories $\cE \liesover
\cB$ assembles into a [[bicategory]], relativising the bicategory of
categories. And, indeed, this is the case: fixing a base $\cB$, we can
put together a bicategory where the objects are categories displayed
over $\cB$, the 1-cells are [[vertical functors]] over $\cB$, and the
2-cells are [[vertical natural transformations]] over $\cB$.

<!--
```agda
private
  Vf : Displayed B o' ℓ' → Displayed B o'' ℓ'' → Precategory _ _
  Vf = Cat↓[_,_]

open Vertical-functor
open make-natural-iso
open Functor
open _=>↓_
open Make-bifunctor
```
-->

We can then extend the *whiskering* operation between vertical natural
transformations to the action of a "composition" functor between
vertical functor categories, with the functoriality condition precisely
as in the nondisplayed case.

```agda
∘V-functor' : ∀ {E F G : Displayed B o' ℓ'} → Functor (Vf F G ×ᶜ Vf E F) (Vf E G)
∘V-functor' .F₀ (G , F) = G ∘V F
∘V-functor' .F₁ (f , g) = f ◆↓ g
∘V-functor' {G = 𝒢} .F-id {F , G} = ext λ x → ap₂ G._∘_ (F .F-id') refl ∙ G.idr _ where
  module G {x} = Cat (Fibre 𝒢 x)
∘V-functor' {F = ℱ} {G = 𝒢} .F-∘ {X , Y} {Z , W} {U , V} (α , β) (δ , γ) = ext λ x →
  U .F₁' (β .η' x F.∘ γ .η' x) G.∘ (α .η' _ G.∘ δ .η' _)          ≡⟨ G.pushl (F-∘↓ U) ⟩
  U .F₁' (β .η' x) G.∘ U .F₁' (γ .η' x) G.∘ α .η' _ G.∘ δ .η' _   ≡⟨ G.extend-inner (sym (is-natural↓ α _ _ _)) ⟩
  U .F₁' (β .η' x) G.∘ α .η' _ G.∘ Z .F₁' (γ .η' _) G.∘ δ .η' _   ≡⟨ G.pulll refl ⟩
  (U .F₁' (β .η' _) G.∘ α .η' _) G.∘ Z .F₁' (γ .η' _) G.∘ δ .η' _ ∎
  where
    module G {x} = Cat (Fibre 𝒢 x) using (_∘_ ; pushl ; extend-inner ; pulll)
    module F {x} = Cat (Fibre ℱ x) using (_∘_)

∘V-functor : ∀ {E F G : Displayed B o' ℓ'} → Bifunctor (Vf F G) (Vf E F) (Vf E G)
∘V-functor = Curry ∘V-functor'
```

<!--
```agda
private
  assoc : Associator-for Vf ∘V-functor
  assoc {C = C} {D = D} = to-natural-iso ni where
    module D = Disp D
    module D' {x} = Cat (Fibre D x)
    module C' {x} = Cat (Fibre C x)

    ni : make-natural-iso {D = Vf _ _} _ _
    ni .eta _ = record { η' = λ x' → D.id' ; is-natural' = λ x y f → D.to-pathp[] D.id-comm[] }
    ni .inv _ = record { η' = λ x' → D.id' ; is-natural' = λ x y f → D.to-pathp[] D.id-comm[] }
    ni .eta∘inv _ = ext λ _ → D'.idl _
    ni .inv∘eta _ = ext λ _ → D'.idl _
    ni .natural x y f = ext λ _ →
        D'.pullr (D'.cancelr (D'.idr _) ∙ ap (x .fst .F₁') (ap₂ C'._∘_ (C'.eliml (y .snd .fst .F-id')) (C'.elimr refl)))
      ∙ sym (D'.eliml refl
        ∙ D'.pullr (D'.pullr (ap₂ D'._∘_ (D'.elimr refl) (D'.elimr refl)) ∙ ap₂ D'._∘_ refl (sym (Vertical-functor.Fibre-map (x .fst) _ .Functor.F-∘ _ _)))
        ∙ D'.pulll (D'.eliml (ap (y .fst .F₁') (y .snd .fst .F-id') ∙ y .fst .F-id') ∙ D'.eliml (y .fst .F-id'))
        ∙ ap₂ D'._∘_ (D'.introl (y .fst .F-id')) refl)
```
-->

Finally, we can put together the bicategory structure itself. This is,
again, exactly as in the nondisplayed case, with all the components of
the structural isomorphisms being identities.

```agda
Disp[] : Prebicategory (o ⊔ ℓ ⊔ lsuc (o' ⊔ ℓ')) (o ⊔ ℓ ⊔ o' ⊔ ℓ') (o ⊔ ℓ ⊔ o' ⊔ ℓ')
Disp[] .Ob = Displayed B o' ℓ'
Disp[] .Hom = Cat↓[_,_]
Disp[] .id = Id'
Disp[] .compose = ∘V-functor
Disp[] .unitor-l {B = B} = to-natural-iso ni where
  module B = Disp B
  ni : make-natural-iso {D = Vf _ _} _ _
  ni .eta _ = record { η' = λ x' → B.id' ; is-natural' = λ x y f → B.to-pathp[] B.id-comm[] }
  ni .inv _ = record { η' = λ x' → B.id' ; is-natural' = λ x y f → B.to-pathp[] B.id-comm[] }
  ni .eta∘inv _ = ext λ _ → Cat.idl (Fibre B _) _
  ni .inv∘eta _ = ext λ _ → Cat.idl (Fibre B _) _
  ni .natural x y f = ext λ _ → Cat.elimr (Fibre B _) refl ∙ Cat.id-comm (Fibre B _)
Disp[] .unitor-r {B = B} = to-natural-iso ni where
  module B = Disp B
  module B' {x} = Cat (Fibre B x) using (_∘_ ; idl ; elimr)

  ni : make-natural-iso {D = Vf _ _} _ _
  ni .eta _ = record { η' = λ x' → B.id' ; is-natural' = λ x y f → B.to-pathp[] B.id-comm[] }
  ni .inv _ = record { η' = λ x' → B.id' ; is-natural' = λ x y f → B.to-pathp[] B.id-comm[] }
  ni .eta∘inv _ = ext λ _ → B'.idl _
  ni .inv∘eta _ = ext λ _ → B'.idl _
  ni .natural x y f = ext λ _ → B'.elimr refl ∙ ap₂ B'._∘_ (y .F-id') refl
Disp[] .associator = assoc
Disp[] .triangle {C = C} f g = ext λ _ → Cat.idr (Fibre C _) _
Disp[] .pentagon {E = E} f g h i = ext λ _ → ap₂ E._∘_
  (E.eliml (ap (f .F₁') (ap (g .F₁') (h .F-id')) ∙∙ ap (f .F₁') (g .F-id') ∙∙ f .F-id'))
  (E.elimr (E.eliml (f .F-id')))
  where module E {x} = Cat (Fibre E x) using (_∘_ ; eliml ; elimr)
```
