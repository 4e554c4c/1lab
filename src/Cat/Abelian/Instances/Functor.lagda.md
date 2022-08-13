```agda
open import Algebra.Group.Ab
open import Algebra.Monoid
open import Algebra.Group

open import Cat.Instances.Functor
open import Cat.Abelian.Functor
open import Cat.Abelian.Base
open import Cat.Prelude

module Cat.Abelian.Instances.Functor
  {o o′ ℓ ℓ′} {A : Precategory o ℓ}   {𝒜 : Ab-category A}
              {B : Precategory o′ ℓ′} {ℬ : Ab-category B}
  where
```

<!--
```agda
private
  module A = Ab-category 𝒜
  module B = Ab-category ℬ
open Precategory
open Ab-category
open Ab-functor
open _=>_
```
-->

# Ab-enriched functor categories

Recall that, for a pair of [$\Ab$-categories] $\ca{A}$ and $\ca{B}$, we
define the [$\Ab$-functors] between them to be the functors $F : \ca{A}
\to \ca{B}$ which additionally preserve homwise addition[^pres-add].
We can, mimicking the construction of the ordinary [functor category],
construct a category $[\ca{A}, \ca{B}]_{\Ab}$ consisting only of the
$\Ab$-functors, and prove that it is _also_ an $\Ab$-category.

[^pres-add]: i.e. those functors $F$ for which, for all $a, b$, the
$\hom$-mapping $F_{a,b} : \ca{A}(a,b) \to \ca{B}(F(a),F(b))$ extends to
a group homomorphism.

[$\Ab$-categories]: Cat.Abelian.Base.html#ab-enriched-categories
[$\Ab$-functors]: Cat.Abelian.Functors.html#ab-enriched-functors
[functor category]: Cat.Instances.Functor.html

```agda
Ab-functors : Precategory _ _
Ab-functors .Ob          = Ab-functor 𝒜 ℬ
Ab-functors .Hom F G     = F .functor => G .functor
Ab-functors .Hom-set _ _ = Nat-is-set
Ab-functors .id    = Cat[ A , B ] .Precategory.id
Ab-functors ._∘_   = Cat[ A , B ] .Precategory._∘_
Ab-functors .idr   = Cat[ A , B ] .Precategory.idr
Ab-functors .idl   = Cat[ A , B ] .Precategory.idl
Ab-functors .assoc = Cat[ A , B ] .Precategory.assoc
```

We can calculate that the natural transformations $F \To G$ between
$\Ab$-functors have a pointwise abelian group structure. The most
important thing to verify is that the pointwise sum of natural
transformations is natural, which follows from multilinearity of the
composition operation.

```agda
[_,_]Ab : Ab-category Ab-functors
[_,_]Ab .Group-on-hom F G = grp where
  open Group-on
  module F = Ab-functor F
  module G = Ab-functor G

  grp : Group-on (F .functor => G .functor)
  grp ._⋆_ f g .η x = f .η x B.+ g .η x
  grp ._⋆_ f g .is-natural x y h =
    (f .η y B.+ g .η y) B.∘ F.₁ h             ≡˘⟨ B.∘-linear-l _ _ _ ⟩
    (f .η y B.∘ F.₁ h) B.+ (g .η y B.∘ F.₁ h) ≡⟨ ap₂ B._+_ (f .is-natural x y h) (g .is-natural x y h) ⟩
    (G.₁ h B.∘ f .η x) B.+ (G.₁ h B.∘ g .η x) ≡⟨ B.∘-linear-r _ _ _ ⟩
    G.₁ h B.∘ (f .η x B.+ g .η x)             ∎
```

Specifically, given $(\eta_x + \eps_x)F(h)$, we can distribute $F(h)$
into the composite, apply naturality to both summands, and distribute
$G(h)$ _out_ of the composite on the left. Similar computations
establish that the pointwise inverse of natural transformations is
natural.

```agda
  grp .has-is-group .is-group.unit .η x = B.0m
  grp .has-is-group .is-group.unit .is-natural x y f = B.∘-zero-l ∙ sym (B.∘-zero-r)

  grp .has-is-group .is-group.inverse f .η x = B.Hom.inverse (f .η x)
  grp .has-is-group .is-group.inverse f .is-natural x y g =
    B.Hom.inverse (f .η y) B.∘ F.₁ g   ≡˘⟨ B.neg-∘-l ⟩
    B.Hom.inverse ⌜ f .η y B.∘ F.₁ g ⌝ ≡⟨ ap! (f .is-natural x y g) ⟩
    B.Hom.inverse (G.₁ g B.∘ f .η x)   ≡⟨ B.neg-∘-r ⟩
    G.₁ g B.∘ B.Hom.inverse (f .η x)   ∎

  grp .has-is-group .is-group.has-is-monoid .has-is-semigroup =
    record { has-is-magma = record { has-is-set = Nat-is-set }
           ; associative  = λ {x y z} → Nat-path (λ x → B.Hom.associative)
           }
  grp .has-is-group .is-group.has-is-monoid .idl = Nat-path λ x → B.Hom.idl
  grp .has-is-group .is-group.has-is-monoid .idr = Nat-path λ x → B.Hom.idr
  grp .has-is-group .is-group.inversel = Nat-path λ x → B.Hom.inversel
  grp .has-is-group .is-group.inverser = Nat-path λ x → B.Hom.inverser

[_,_]Ab .Hom-grp-ab F G f g = Nat-path λ x → B.Hom.commutative
[_,_]Ab .∘-linear-l f g h = Nat-path λ x → B.∘-linear-l _ _ _
[_,_]Ab .∘-linear-r f g h = Nat-path λ x → B.∘-linear-r _ _ _
```
