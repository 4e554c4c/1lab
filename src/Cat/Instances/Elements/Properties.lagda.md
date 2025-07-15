<!--
```agda
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Equivalence
open import Cat.Prelude
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Terminal
open import Cat.Functor.Constant


open import Cat.Instances.Elements
```
-->

```agda
module Cat.Instances.Elements.Properties {o ℓ s} {C : Precategory o ℓ} where
```

<!--
```agda
open Terminal (Sets-terminal {ℓ = s}) renaming (top to ★)
open Precategory C
open Functor
open is-precat-iso
open is-iso
```
-->

# Special categories of elements

The [[category of elements]] for the constant functor is exactly $\cC$.
In particular, the projection is an isomorphism.

```agda
elements-terminal-is-iso : is-precat-iso (πₚ C $ Const ★)
elements-terminal-is-iso .has-is-iso = is-iso→is-equiv i where
  i : is-iso (F₀ (πₚ C $ Const ★))
  i .from x = elem x (lift tt)
  i .rinv _ = refl
  i .linv _ = refl
elements-terminal-is-iso .has-is-ff = is-iso→is-equiv i where
  i : is-iso (F₁ (πₚ C $ Const ★))
  i .from f = elem-hom f refl
  i .rinv _ = refl
  i .linv _ = Element-hom-path _ _ refl
```
