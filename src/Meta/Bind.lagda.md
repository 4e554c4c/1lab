<!--
```agda
open import 1Lab.Type

open import Meta.Idiom
```
-->

```agda
module Meta.Bind where
```

# Primitive: `do` syntax

```agda
private variable
  ℓ ℓ' : Level
  A B C : Type ℓ

record Bind (M : Effect) : Typeω where
  private module M = Effect M
  field
    _>>=_ : M.₀ A → (A → M.₀ B) → M.₀ B
    ⦃ Idiom-bind ⦄ : Idiom M


  _>>_ : M.₀ A → M.₀ B → M.₀ B
  _>>_ f g = f >>= λ _ → g

  infixl 1 _>>=_

  _=<<_ : (A → M.₀ B) → M.₀ A → M.₀ B
  _=<<_ f x = x >>= f

  _>=>_ : (A → M.₀ B) → (B → M.₀ C) → (A → M.₀ C)
  (f >=> g) a = f a >>= g

  _<=<_ : (B → M.₀ C) → (A → M.₀ B) → (A → M.₀ C)
  f <=< g = g >=> f

  infixr 1 _=<<_ _<=<_ _>=>_

open Bind ⦃ ... ⦄ public
```
