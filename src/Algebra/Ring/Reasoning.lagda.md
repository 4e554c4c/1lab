<!--
```agda
open import 1Lab.Prelude hiding (_*_ ; _+_ ; _-_)

open import Algebra.Monoid
open import Algebra.Ring
```
-->

```agda
module Algebra.Ring.Reasoning {ℓ} (R : Ring ℓ) where
```

# Reasoning combinators for rings

<!--
```agda
open Ring-on (R .snd) public

private variable
  a b c x y z : ⌞ R ⌟
```
-->

```agda
*-zerol : 0r * x ≡ 0r
*-zerol {x} =
  0r * x                       ≡⟨ a.introl a.inversel ⟩
  (- 0r * x) + 0r * x + 0r * x ≡⟨ a.pullr (sym *-distribr) ⟩
  (- 0r * x) + (0r + 0r) * x   ≡⟨ ap₂ _+_ refl (ap (_* x) a.idl) ⟩
  (- 0r * x) + 0r * x          ≡⟨ a.inversel ⟩
  0r                           ∎

*-zeror : x * 0r ≡ 0r
*-zeror {x} =
  x * 0r                     ≡⟨ a.intror a.inverser ⟩
  x * 0r + (x * 0r - x * 0r) ≡⟨ a.pulll (sym *-distribl) ⟩
  x * (0r + 0r) - x * 0r     ≡⟨ ap₂ _-_ (ap (x *_) a.idl) refl ⟩
  x * 0r - x * 0r            ≡⟨ a.inverser ⟩
  0r                         ∎

*-negatel : (- x) * y ≡ - (x * y)
*-negatel {x} {y} = monoid-inverse-unique a.has-is-monoid (x * y) ((- x) * y) (- (x * y))
  (sym *-distribr ∙∙ ap (_* y) a.inversel ∙∙ *-zerol)
  a.inverser

*-negater : x * (- y) ≡ - (x * y)
*-negater {x} {y} = monoid-inverse-unique a.has-is-monoid (x * y) (x * (- y)) (- (x * y))
  (sym *-distribl ∙∙ ap (x *_) a.inversel ∙∙ *-zeror)
  a.inverser

module _ (p : y ≡ 0r) where
  *absorbr : x * y ≡ 0r
  *absorbr = ap (_ *_) p ∙ *-zeror

  *absorbl : y * x ≡ 0r
  *absorbl = ap (_* _) p ∙ *-zerol

  +insertl : x ≡ x + y
  +insertl = sym $ ap (_ +_) p ∙ +-idr

  +insertr : x ≡ y + x
  +insertr = sym $ ap (_+ _) p ∙ +-idl

  +eliml : x + y ≡ x
  +eliml = ap (_ +_) p ∙ +-idr

  +elimr : y + x ≡ x
  +elimr = ap (_+ _) p ∙ +-idl

module _ (a+b≡c : a + b ≡ c) where abstract
  +pulll : a + (b + x) ≡ c + x
  +pulll {x = x} =
    a + (b + x) ≡⟨ +-associative ⟩
   (a + b) + x  ≡⟨ ap (_+ x) a+b≡c ⟩
    c + x       ∎

  +pullr : (x + a) + b ≡ x + c
  +pullr {x = x} =
    x + a + b   ≡⟨ sym +-associative ⟩
    x + (a + b) ≡⟨ ap (x +_) a+b≡c ⟩
    x + c       ∎

_⟩+⟨_ : a ≡ b → x ≡ y → a + x ≡ b + y
_⟩+⟨_ = ap₂ _+_

infixl 20 _⟩+⟨_

refl⟩+⟨_ : a ≡ b → x + a ≡ x + b
refl⟩+⟨_ p = refl ⟩+⟨ p

_⟩+⟨refl : a ≡ b → a + x ≡ b + x
_⟩+⟨refl p = p ⟩+⟨ refl

infix 22 refl⟩+⟨_
infix 21 _⟩+⟨refl


  --*insertl : x ≡ x * y
  --*insertl = sym *absorbr
```
