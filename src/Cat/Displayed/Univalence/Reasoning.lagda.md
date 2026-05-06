<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Univalence
import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Univalence.Reasoning
  {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ')
  where
```

# Remarks about displayed univalence

Note that, over a univalent base, [[univalence of displayed categories]]
is equivalent to _fibrewise_ univalence; Over a precategorical base,
displayed univalence is a stronger condition, but it still implies that
each fibre is univalent. Moreover, since isomorphisms in fibres are
equivalent to [vertical isomorphisms], if $\cE$ is a [[displayed
univalent category]], then vertical isomorphism is an [[identity
system]] on each type of objects-over.

[vertical isomorphisms]: Cat.Displayed.Morphism.html#isos

<!--
```agda
private module B = Cr B

open Cat.Displayed.Univalence E
open Cat.Displayed.Reasoning E
open Cat.Displayed.Morphism E
open _≅[_]_
```
-->

```agda
≅↓-identity-system
  : ∀ {x} → is-category-displayed
  → is-identity-system (_≅↓_ {x = x}) (λ _ → id-iso↓)
≅↓-identity-system e-cat .to-path {a} {b} i =
  ap fst $ e-cat B.id-iso a (a , id-iso↓) (b , i)
≅↓-identity-system e-cat .to-path-over {a} {b} i =
  ap snd $ e-cat B.id-iso a (a , id-iso↓) (b , i)
```

Therefore, we have an equivalence between paths of objects-over the same
base object and vertical isomorphisms, regardless of whether the base
category is univalent or not. Much like in the non-displayed case, this
equivalence lets us compute transports of morphisms-over (along their
domain and codomain, rather than over their base morphism) in terms of
pre/post-composition with a vertical isomorphism.

```agda
path→vertical-iso
  : ∀ {x} {x₁ x₂ : Ob[ x ]} → x₁ ≡ x₂ → x₁ ≅↓ x₂
path→vertical-iso {x₁ = x₁} p = transport (λ i → x₁ ≅↓ p i) id-iso↓

vertical-iso→path
  : ∀ {x} {x₁ x₂ : Ob[ x ]}
  → is-category-displayed
  → x₁ ≅↓ x₂ → x₁ ≡ x₂
vertical-iso→path e = ≅↓-identity-system e .to-path
```

The transport and dependent path lemmas are straightforward
generalisations of [[their non-displayed counterparts|transport in
Hom]]. Note that while we only need to talk about vertical isomorphisms,
the proofs work over an arbitrary morphism in the base. They are also
generalised over an arbitrary identification between e.g. $f = 1f1$ in
the base.

<!--
```agda
private variable
  x y : B.Ob
  f : B.Hom x y
  x₁ x₂ y₁ y₂ x' y' : Ob[ x ]
```
-->

```agda
abstract
  Hom[]-transport
    : (α : f ≡ B.id B.∘ f B.∘ B.id) (p : x₁ ≡ x₂) (q : y₁ ≡ y₂)
    → (f' : Hom[ f ] x₁ y₁)
    → transport (λ i → Hom[ f ] (p i) (q i)) f' ≡[ α ]
      path→vertical-iso q .to' ∘' f' ∘' path→vertical-iso p .from'

  Hom[]-pathp-iso
    : (e-cat : is-category-displayed)
    → (α : B.id B.∘ f B.∘ B.id ≡ f)
    → (p : x₁ ≅↓ x₂) (q : y₁ ≅↓ y₂) (f' : Hom[ f ] x₁ y₁) (g' : Hom[ f ] x₂ y₂)
    → q .to' ∘' f' ∘' p .from' ≡[ α ] g'
    → PathP (λ i → Hom[ f ] (vertical-iso→path e-cat p i)
                            (vertical-iso→path e-cat q i))
        f' g'

  Hom[]-pathp-refll-iso
    : (e-cat : is-category-displayed) (α : f B.∘ B.id ≡ f)
    → (p : x₁ ≅↓ x₂) (f' : Hom[ f ] x₁ y') (g' : Hom[ f ] x₂ y')
    → f' ∘' p .from' ≡[ α ] g'
    → PathP (λ i → Hom[ f ] (vertical-iso→path e-cat p i) y') f' g'

  Hom[]-pathp-reflr-iso
    : (e-cat : is-category-displayed) (α : B.id B.∘ f ≡ f)
    → (p : y₁ ≅↓ y₂) (f' : Hom[ f ] x' y₁) (g' : Hom[ f ] x' y₂)
    → p .to' ∘' f' ≡[ α ] g'
    → PathP (λ i → Hom[ f ] x' (vertical-iso→path e-cat p i)) f' g'
```

<details>
<summary>These lemmas all have scary type signatures and **nightmare**
proofs. Therefore, they're hidden away down here.</summary>

```agda
  Hom[]-transport {f = f} {x₁ = x₁} {y₁ = y₁} α p q f' =
    J₂ (λ x₂ y₂ p q → transport (λ i → Hom[ f ] (p i) (q i)) f'
               ≡[ α ] path→vertical-iso q .to' ∘' f' ∘' path→vertical-iso p .from')
      (to-pathp⁻ (sym
        (ap (subst (λ e → Hom[ e ] _ _) _)
          (  from-pathp⁻ (eliml' refl (transport-refl _) {q = B.idl _})
          ∙∙ ap (subst (λ e → Hom[ e ] _ _) _) (from-pathp⁻ (elimr' refl (transport-refl _) {q = B.idr f}))
          ∙∙ sym (subst-∙ (λ e → Hom[ e ] _ _) _ _ _))
        ∙∙ sym (subst-∙ (λ e → Hom[ e ] _ _) _ _ _)
        ∙∙ ap (λ p → subst (λ e → Hom[ e ] _ _) p f') prop!)))
      p q

  Hom[]-pathp-refll-iso e-cat α p f' g' β = to-pathp $
       from-pathp⁻ (Hom[]-transport (sym (B.idl _ ∙ α)) (vertical-iso→path e-cat p) refl f')
    ∙∙ ap (subst (λ e → Hom[ e ] _ _) _) (
        ap₂ (λ a b → a ∘' f' ∘' b) (transport-refl _)
          (from-pathp (λ i → ≅↓-identity-system e-cat .to-path-over p i .from'))
        ∙ from-pathp⁻ (idl' (f' ∘' p .from')))
    ∙∙ ( sym (subst-∙ (λ e → Hom[ e ] _ _) _ _ _)
      ∙∙ ap (λ α → subst (λ e → Hom[ e ] _ _) α (f' ∘' p .from')) prop!
      ∙∙ from-pathp β)

  Hom[]-pathp-iso e-cat α p q f' g' β = to-pathp $
       from-pathp⁻ (Hom[]-transport (sym α) (vertical-iso→path e-cat p) (vertical-iso→path e-cat q) f')
    ∙∙ ap (subst (λ e → Hom[ e ] _ _) _) (ap₂ (λ a b → a ∘' f' ∘' b)
        (from-pathp (λ i → ≅↓-identity-system e-cat .to-path-over q i .to'))
        (from-pathp (λ i → ≅↓-identity-system e-cat .to-path-over p i .from')))
    ∙∙ from-pathp β

  Hom[]-pathp-reflr-iso {f = f} {x' = x'} e-cat α p f' g' β = {! ≅↓-identity-system e-cat .to-path-over (id-iso↓ {x' = x'}) !}
    where
      foo : PathP (λ i → Hom[ f ] (vertical-iso→path e-cat (id-iso↓ {x' = x'}) i) (vertical-iso→path e-cat p i)) f' g'
      foo = Hom[]-pathp-iso e-cat (B.pulll α ∙ B.idr _) id-iso↓ p f' g' $ begin[]
        p .to' ∘' f' ∘' id'
        ≡[]⟨ refl⟩∘'⟨ idr' _ ⟩
        p .to' ∘' f'
        ≡[]⟨ β ⟩
        g'
        ∎[]
  ```
</details>
