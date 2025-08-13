<!--
```agda
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring
open import Algebra.Ring.Ideal
open import Algebra.Ring.Ideal.Properties
open import Algebra.Ring.Cat.Limits

open import Algebra.Ring.Quotient

open import Cat.Diagram.Coequaliser.RegularEpi
open import Cat.Diagram.Pullback.Properties
open import Cat.Displayed.Univalence.Thin
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Pullback
open import Cat.Prelude hiding (_+_ ; _*_; _-_)
open import Cat.Regular
open import Cat.Morphism.Strong.Epi
open import Cat.Morphism.Factorisation

open import Data.Int.Properties
open import Data.Int.Base

import Algebra.Ring.Reasoning as Kit

import Cat.Displayed.Instances.Subobjects
import Data.Nat as Nat
import Prim.Data.Nat as Nat
import Algebra.Ring.Reasoning as Ringr
```
-->

```agda
module Algebra.Ring.Cat.Regular where
```

<!--
```agda
private variable ℓ : Level
private open module Sor {ℓ} = Cat.Displayed.Instances.Subobjects (Rings ℓ)
open is-regular
open is-coequaliser
open Factorisation
open is-regular-epi renaming (r to nadir)
```
-->

```agda

Subring : Ring ℓ → Type (lsuc ℓ)
Subring R = Subobject R

module _ {Q R : Ring ℓ} (f : Rings.Hom Q R) where
  private
    module f = RingHom f
    open module R = Ringr R
    module Q = Ringr Q

  open is-ring-hom
  open Subobject
  open is-ideal
  open Ideal

  im[_]ʳ : Subring R
  im[_]ʳ .domain = Q /ᴿ Kernel f
  im[_]ʳ .map .fst = coim-rec module _ where
    private abstract
      coh : (x y : ∣ Q .fst ∣) (r : □ (f .fst (x Q.+ (Q.- y)) ≡ 0r)) → f .fst x ≡ f .fst y
      coh = elim! λ x y r → f.from-zero-diff r

    coim-rec = Quot-elim (λ _ → has-is-set) (apply f) coh
  im[_]ʳ .map .snd .pres-id = f.pres-id
  im[_]ʳ .map .snd .pres-+ = elim! λ x y → f.pres-+ x y
  im[_]ʳ .map .snd .pres-* = elim! λ x y → f.pres-* x y
  im[_]ʳ .monic g h x = ext λ a →
    let
      w : (x y : ⌞ Q /ᴿ Kernel f ⌟) → coim-rec x ≡ coim-rec y → x ≡ y
      w = elim! λ a b p → quot (inc (f.pres-diff ∙ ap (λ x → f .fst a - x) (sym p) ∙ +-invr))
    in w (g .fst a) (h .fst a) (unext x a)

module _ {ℓ} {A B : Ring ℓ} (f : Rings.Hom A B) (f-surj : is-surjective (apply f)) where
  private
    module kp = Pullback (Rings-pullbacks f f)
    module B = Ringr B
    module A = Ringr A
    module f = RingHom f

  is-surjective→is-regular-epi : is-regular-epi (Rings _) f
  is-surjective→is-regular-epi .nadir = kp.apex
  is-surjective→is-regular-epi .arr₁ = kp.p₁
  is-surjective→is-regular-epi .arr₂ = kp.p₂
  is-surjective→is-regular-epi .has-is-coeq = done where
    go
      : ∀ {F} (e' : Rings.Hom A F)
      → (p : e' Rings.∘ kp.p₁ ≡ e' Rings.∘ kp.p₂) (x : ⌞ B ⌟)
      → ∥ fibre (apply f) x ∥ → ⌞ F ⌟
    go e' p x = ∥-∥-rec-set (hlevel 2) (λ (f , _) → e' · f) λ (x , α) (y , β) → unext p x y (α ∙ sym β)

    done : is-coequaliser (Rings _) kp.p₁ kp.p₂ f
    done .coequal = ext λ _ _ p → p
    done .universal {e' = e'} p .fst x = go e' p x (f-surj x)
    done .universal {F = F} {e' = e'} comm .snd = record where
      module F = Ringr F
      module e' = RingHom e'

      fn = go e' comm

      pres-id    = case (f-surj B.1r) return (λ e → fn B.1r e ≡ F.1r) of λ x α → unext comm x A.1r (α ∙ sym f.pres-id) ∙ e'.pres-id
      pres-+ a b =
        let
          work : ∀ p q r → fn (a B.+ b) p ≡ fn a q F.+ fn b r
          work = elim! λ ab p a q b r → unext comm ab (a A.+ b) (p ∙ ap₂ B._+_ (sym q) (sym r) ∙ sym (f.pres-+ _ _)) ∙ e'.pres-+ a b
        in work (f-surj (a B.+ b)) (f-surj a) (f-surj b)
      pres-* a b =
        let
          work : ∀ p q r → fn (a B.* b) p ≡ fn a q F.* fn b r
          work = elim! λ ab p a q b r → unext comm ab (a A.* b) (p ∙ ap₂ B._*_ (sym q) (sym r) ∙ sym (f.pres-* _ _)) ∙ e'.pres-* a b
        in work (f-surj (a B.* b)) (f-surj a) (f-surj b)
    done .factors {e' = e'} {p = p} = ext λ x → case (f-surj (f · x)) return (λ e → go e' p (f · x) e ≡ e' · x) of λ x α → unext p _ _ α
    done .unique {e' = e'} {p} {colim} q = ext λ x → case (f-surj x) return (λ e → colim · x ≡ go e' p x e) of λ x α → ap· colim (sym α) ∙ unext q _

is-strong-epi→is-surjective
  : ∀ {ℓ} {A B : Ring ℓ} (f : Rings.Hom A B)
  → is-strong-epi (Rings _) f
  → is-surjective (apply f)
is-strong-epi→is-surjective {A = A} f f-str b =
  do
    (f^* , α) ← inc-is-surjective (inv.inv · b)
    inc (f^* , ap· (im[ f ]ʳ .map) α ∙ unext inv.invl b)
  where
    rem₁ : Rings.is-invertible (im[ f ]ʳ .map)
    rem₁ = is-strong-epi→is-extremal-epi (Rings _) f-str
      record { monic = im[ f ]ʳ .monic } (inclᴿ A _)
      (ext λ _ → refl)
    module inv = Rings.is-invertible rem₁

goal : is-regular (Rings ℓ)
goal {ℓ = ℓ} .factor {Q} {R} f = record where
  module pb = Pullback (Rings-pullbacks f f)
  module Q = Ringr Q
  module f = RingHom f

  mediating = Q /ᴿ Kernel f
  mediate   = inclᴿ Q (Kernel f)
  forget    = im[ f ]ʳ .map

  mediate∈E = □.inc
    $ is-regular-epi→is-strong-epi (Rings ℓ) mediate
    $ is-surjective→is-regular-epi mediate inc-is-surjective

  forget∈M  = inc (im[ f ]ʳ .monic)
  factors   = ext (λ x → refl)
goal .stable = done where
  module _ {A B X : Ring ℓ} (f : Rings.Hom A B) (g : Rings.Hom X B) (f-str : is-strong-epi (Rings _) f) where
    module pb = Pullback (Rings-pullbacks g f)

    rem₃ : is-surjective (apply pb.p₁)
    rem₃ x = do
      (f^*fx , α) ← is-strong-epi→is-surjective f f-str (g · x)
      inc (((x , f^*fx) , sym α) , refl)

    rem₄ : is-strong-epi (Rings ℓ) pb.p₁
    rem₄ = is-regular-epi→is-strong-epi (Rings ℓ) pb.p₁ (is-surjective→is-regular-epi pb.p₁ rem₃)

  done = canonically-stable (is-strong-epi (Rings _))
    (Structured-objects-is-category _) Rings-pullbacks
    rem₄
goal .has-is-lex = Rings-finitely-complete

```
