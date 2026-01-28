<!--
```agda
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Closure
open import 1Lab.Reflection
open import 1Lab.Underlying
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type hiding (id ; _∘_)

open import Cat.Base

open import Data.Fin.Product
open import Data.Fin.Base
```
-->

```agda
module Cat.Displayed.Multi.Base where
```

# Displayed multicategories {defines=displayed-multicategory}

<!--
```agda
Πᶠ' : ∀ {n ℓ} (P : (i : Fin n) → Type ℓ) → Type ℓ
Πᶠ' {n = 0} P     = Lift _ ⊤
Πᶠ' {n = suc n} P = P fzero × Πᶠ' λ i → P (fsuc i)
```
-->

```agda
record MultiDisplayed {o ℓ} (B : Precategory o ℓ)
                 (o' ℓ' : Level) : Type (o ⊔ ℓ ⊔ lsuc o' ⊔ lsuc ℓ') where
  no-eta-equality
  open Precategory B
  field
    Ob[_] : Ob → Type o'
    MHom[_] : ∀ (xs : List Ob) → ∀ {y} → Πᶠ' (λ i → Hom (xs ! i) y) → Πᶠ' (λ i → Ob[ xs ! i ]) → Ob[ y ] → Type ℓ'
{-
    Hom[_]-set : ∀ {a b} (f : Hom a b) (x : Ob[ a ]) (y : Ob[ b ])
               → is-set (Hom[ f ] x y)
    id' : ∀ {a} {x : Ob[ a ]} → Hom[ id ] x x

    _∘'_ : ∀ {a b c x y z} {f : Hom b c} {g : Hom a b}
         → Hom[ f ] y z → Hom[ g ] x y → Hom[ f ∘ g ] x z
  infixr 40 _∘'_

  _≡[_]_ : ∀ {a b x y} {f g : Hom a b} → Hom[ f ] x y → f ≡ g → Hom[ g ] x y → Type ℓ'
  _≡[_]_ {a} {b} {x} {y} f' p g' = PathP (λ i → Hom[ p i ] x y) f' g'

  infix 30 _≡[_]_
  field
    idr' : ∀ {a b x y} {f : Hom a b} (f' : Hom[ f ] x y) → (f' ∘' id') ≡[ idr f ] f'
    idl' : ∀ {a b x y} {f : Hom a b} (f' : Hom[ f ] x y) → (id' ∘' f') ≡[ idl f ] f'
    assoc'
      : ∀ {a b c d w x y z} {f : Hom c d} {g : Hom b c} {h : Hom a b}
      → (f' : Hom[ f ] y z) (g' : Hom[ g ] x y) (h' : Hom[ h ] w x)
      → f' ∘' (g' ∘' h') ≡[ assoc f g h ] ((f' ∘' g') ∘' h')
  field
    hom[_]
      : ∀ {a b x y} {f g : Hom a b} (p : f ≡ g) (f' : Hom[ f ] x y)
      → Hom[ g ] x y
    coh[_]
      : ∀ {a b x y} {f g : Hom a b} (p : f ≡ g) (f' : Hom[ f ] x y)
      → f' ≡[ p ] hom[ p ] f'
  _∙[]_ : ∀ {a b x y} {f g h : Hom a b} {p : f ≡ g} {q : g ≡ h}
        → {f' : Hom[ f ] x y} {g' : Hom[ g ] x y} {h' : Hom[ h ] x y}
        → f' ≡[ p ] g' → g' ≡[ q ] h' → f' ≡[ p ∙ q ] h'
  _∙[]_ {x = x} {y = y} p' q' = _∙P_ {B = λ f → Hom[ f ] x y} p' q'

  ∙[-]-syntax : ∀ {a b x y} {f g h : Hom a b} (p : f ≡ g) {q : g ≡ h}
        → {f' : Hom[ f ] x y} {g' : Hom[ g ] x y} {h' : Hom[ h ] x y}
        → f' ≡[ p ] g' → g' ≡[ q ] h' → f' ≡[ p ∙ q ] h'
  ∙[-]-syntax {x = x} {y = y} p p' q' = _∙P_ {B = λ f → Hom[ f ] x y} p' q'

  ≡[]⟨⟩-syntax : ∀ {a b x y} {f g h : Hom a b} {p : f ≡ g} {q : g ≡ h}
               → (f' : Hom[ f ] x y) {g' : Hom[ g ] x y} {h' : Hom[ h ] x y}
               → g' ≡[ q ] h' → f' ≡[ p ] g' → f' ≡[ p ∙ q ] h'
  ≡[]⟨⟩-syntax f' q' p' = p' ∙[] q'

  ≡[-]⟨⟩-syntax : ∀ {a b x y} {f g h : Hom a b} (p : f ≡ g) {q : g ≡ h}
               → (f' : Hom[ f ] x y) {g' : Hom[ g ] x y} {h' : Hom[ h ] x y}
               → g' ≡[ q ] h' → f' ≡[ p ] g' → f' ≡[ p ∙ q ] h'
  ≡[-]⟨⟩-syntax f' p q' p' = p' ∙[] q'

  _≡[]˘⟨_⟩_ : ∀ {a b x y} {f g h : Hom a b} {p : g ≡ f} {q : g ≡ h}
            → (f' : Hom[ f ] x y) {g' : Hom[ g ] x y} {h' : Hom[ h ] x y}
            → g' ≡[ p ] f' → g' ≡[ q ] h' → f' ≡[ sym p ∙ q ] h'
  f' ≡[]˘⟨ p' ⟩ q' = symP p' ∙[] q'

  syntax ∙[-]-syntax p p' q' = p' ∙[ p ] q'
  syntax ≡[]⟨⟩-syntax f' q' p' = f' ≡[]⟨ p' ⟩ q'
  syntax ≡[-]⟨⟩-syntax p f' q' p' = f' ≡[ p ]⟨ p' ⟩ q'

  infixr 30 _∙[]_ ∙[-]-syntax
  infixr 2 ≡[]⟨⟩-syntax ≡[-]⟨⟩-syntax _≡[]˘⟨_⟩_
-}
```

