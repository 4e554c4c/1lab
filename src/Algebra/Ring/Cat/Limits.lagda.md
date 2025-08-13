<!--
```agda
open import Cat.Displayed.Univalence.Thin
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Equaliser
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Displayed.Total
open import Cat.Prelude hiding (_+_ ; _*_)

open import Algebra.Ring

import Algebra.Ring.Reasoning as Ringr

open is-ring-hom
open is-product
open make-ring
open Terminal
open Equaliser
open is-equaliser
open Product
```
-->

```agda
module Algebra.Ring.Cat.Limits where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
```
-->

# Limits of rings

```agda
⊤ᴿ : Ring ℓ
⊤ᴿ .fst = el! (Lift _ ⊤)
⊤ᴿ .snd = to-ring-on λ where
  .ring-is-set → hlevel 2
  .0R               → _
  ._+_              → _
  .-_               → _
  .1R               → _
  ._*_              → _
  .+-idl x          → refl
  .+-invr x         → refl
  .+-assoc x y z    → refl
  .+-comm x y       → refl
  .*-idl x          → refl
  .*-idr x          → refl
  .*-assoc x y z    → refl
  .*-distribl x y z → refl
  .*-distribr x y z → refl

Rings-terminal : Terminal (Rings ℓ)
Rings-terminal .top = ⊤ᴿ
Rings-terminal .has⊤ x .centre = ∫hom (λ _ → _) record
  { pres-id = refl
  ; pres-+  = λ _ _ → refl
  ; pres-*  = λ _ _ → refl
  }
Rings-terminal .Terminal.has⊤ x .paths h = ext λ _ → refl

_×ᴿ_ : Ring ℓ → Ring ℓ' → Ring (ℓ ⊔ ℓ')
(A ×ᴿ B) .fst = el! (⌞ A ⌟ × ⌞ B ⌟)
(A ×ᴿ B) .snd = to-ring-on record where
  ring-is-set = hlevel 2

  module A = Ringr A
  module B = Ringr B

  0R = A.0r , B.0r
  1R = (A.1r , B.1r)
  _+_ (a , x) (b , y) = a A.+ b , x B.+ y
  _*_ (a , x) (b , y) = a A.* b , x B.* y
  -_  (a , x) = A.- a , B.- x

  +-idl x          = A.+-idl         ,ₚ B.+-idl
  +-invr x         = A.+-invr        ,ₚ B.+-invr
  +-assoc x y z    = A.+-associative ,ₚ B.+-associative
  +-comm x y       = A.+-commutes    ,ₚ B.+-commutes
  *-idl x          = A.*-idl         ,ₚ B.*-idl
  *-idr x          = A.*-idr         ,ₚ B.*-idr
  *-assoc x y z    = A.*-associative ,ₚ B.*-associative
  *-distribl x y z = A.*-distribl    ,ₚ B.*-distribl
  *-distribr x y z = A.*-distribr    ,ₚ B.*-distribr

Rings-products : has-products (Rings ℓ)
Rings-products A B .apex = A ×ᴿ B
Rings-products A B .π₁ .fst = fst
Rings-products A B .π₁ .snd = record
  { pres-id = refl
  ; pres-+  = λ x y → refl
  ; pres-*  = λ x y → refl
  }
Rings-products A B .π₂ .fst = snd
Rings-products A B .π₂ .snd = record
  { pres-id = refl
  ; pres-+  = λ x y → refl
  ; pres-*  = λ x y → refl
  }
Rings-products A B .has-is-product .⟨_,_⟩ f g .fst x = f · x , g · x
Rings-products A B .has-is-product .⟨_,_⟩ f g .snd = record where
  pres-id    = f .snd .pres-id    ,ₚ g .snd .pres-id
  pres-+ x y = f .snd .pres-+ x y ,ₚ g .snd .pres-+ x y
  pres-* x y = f .snd .pres-* x y ,ₚ g .snd .pres-* x y
Rings-products A B .has-is-product .π₁∘⟨⟩ = ext λ _ → refl
Rings-products A B .has-is-product .π₂∘⟨⟩ = ext λ _ → refl
Rings-products A B .has-is-product .unique p q = ext λ _ → unext p _ ,ₚ unext q _

Rings-equalisers : has-equalisers (Rings ℓ)
Rings-equalisers {a = A} {B} f g = done where
  module A = Ringr A
  module B = Ringr B
  module f = RingHom f
  module g = RingHom g
  Eqᴿ : Ring _
  Eqᴿ .fst = el! (Σ[ x ∈ A ] f · x ≡ g · x)
  Eqᴿ .snd = to-ring-on λ where
    .ring-is-set         → hlevel 2
    .0R                  → A.0r , f.pres-0 ∙ sym g.pres-0
    ._+_ (x , p) (y , q) → x A.+ y , f.pres-+ _ _ ∙ ap₂ B._+_ p q ∙ sym (g.pres-+ _ _)
    .-_  (x , p)         → A.- x , f.pres-neg ∙ ap B.-_ p ∙ sym g.pres-neg
    .1R                  → A.1r , f.pres-id ∙ sym g.pres-id
    ._*_ (x , p) (y , q) → x A.* y , f.pres-* _ _ ∙ ap₂ B._*_ p q ∙ sym (g.pres-* _ _)
    .+-idl x          → Σ-prop-path! A.+-idl
    .+-invr x         → Σ-prop-path! A.+-invr
    .+-assoc x y z    → Σ-prop-path! A.+-associative
    .+-comm x y       → Σ-prop-path! A.+-commutes
    .*-idl x          → Σ-prop-path! A.*-idl
    .*-idr x          → Σ-prop-path! A.*-idr
    .*-assoc x y z    → Σ-prop-path! A.*-associative
    .*-distribl x y z → Σ-prop-path! A.*-distribl
    .*-distribr x y z → Σ-prop-path! A.*-distribr

  done : Equaliser (Rings _) f g
  done .apex = Eqᴿ
  done .equ .fst = fst
  done .equ .snd = record
    { pres-id = refl
    ; pres-+  = λ _ _ → refl
    ; pres-*  = λ _ _ → refl
    }
  done .has-is-eq .equal = ext λ _ p → p
  done .has-is-eq .universal {e' = e'} p .fst x = record
    { fst = e' · x
    ; snd = unext p x
    }
  done .has-is-eq .universal {e' = e'} p .snd = record where
    pres-id    = Σ-prop-path! (e' .snd .pres-id)
    pres-+ x y = Σ-prop-path! (e' .snd .pres-+ _ _)
    pres-* x y = Σ-prop-path! (e' .snd .pres-* _ _)
  done .has-is-eq .factors = ext λ _ → refl
  done .has-is-eq .unique p = ext λ _ → Σ-prop-path! (unext p _)

Rings-finitely-complete : Finitely-complete (Rings ℓ)
Rings-finitely-complete = with-equalisers _
  Rings-terminal
  Rings-products
  Rings-equalisers

Rings-pullbacks : has-pullbacks (Rings ℓ)
Rings-pullbacks = Finitely-complete.pullbacks Rings-finitely-complete
```
