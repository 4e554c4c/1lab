<!--
```agda
open import 1Lab.Path.IdentitySystem
open import 1Lab.HLevel.Closure
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Path.IdentitySystem.Equiv where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' ℓ''' : Level
  A : Type ℓ'
  R : A → A → Type ℓ'
  r : ∀ a → R a a
```
-->

# Equivalence in alternative identity systems

```agda
module EquivOver
  {A : Type ℓ}   {R  : A → A → Type ℓ'}   {r  : ∀ a → R a a}
  {B : Type ℓ''} {R' : B → B → Type ℓ'''} {r' : ∀ b → R b b}
  (ida : is-identity-system R r)
  (idb : is-identity-system R r)
  where

  module ida = is-identity-system ida
  module idb = is-identity-system idb

  fibre' : (A → B) → B → Type _
  fibre' f y = Σ[ x ∈ A ] R' (f x) y


  -- what do we need
  record R'-pathp-thing (f : A → B) {a b c} (p : R a b) (r1 : R' (f a) c) (r' : R' (f b) c) : Type _ where
    field
      blah : {! !}

  record fibre-is-contr' (f : A → B) (y : B) : Type (ℓ ⊔ ℓ') where
    constructor contr'
    field
      centre' : (fibre' f y)
      paths'  : (x : fibre' f y) → Σ[ p ∈ R (centre' .fst) (x .fst) ] {! centre' .snd!}


  record is-equiv (f : A → B) : Type (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ ℓ''') where
    no-eta-equality
    field
      is-eqv : (y : B) → fibre-is-contr' f y



```
