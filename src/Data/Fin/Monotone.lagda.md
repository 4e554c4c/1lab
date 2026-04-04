<!--
```agda
--open import 1Lab.Reflection.List
--open import 1Lab.Path.Cartesian
open import 1Lab.Prelude

--open import Data.Maybe.Properties
--open import Data.List.Membership
--open import Data.Set.Coequaliser
open import Data.Fin.Properties
--open import Data.Fin.Closure
--open import Data.Fin.Product
--open import Data.List.Sigma
open import Data.Bool.Base
--open import Data.List.Base
open import Data.Fin.Base
open import Data.Nat.Base renaming (_≤_ to _≤n_; _<_ to _<n_)
open import Data.Nat.Properties
open import Data.Nat.Order
--open import Data.List.Pi
open import Data.Maybe
open import Data.Dec
open import Data.Irr
open import Data.Sum
open import Prim.Data.Nat using () renaming (_<_ to _<?_)

open import Order.Instances.Nat using (Nat-poset)
```
-->

```agda
module Data.Fin.Monotone where
```

<!--
```agda
private variable
  ℓ : Level
  n m k : Nat
```
-->
```agda

open import Order.Reasoning Nat-poset using
  ( _≤⟨_⟩_
  ; _=⟨_⟩_
  ; _=˘⟨_⟩_
  ; _≤∎    )

record is-suc (j : Fin n) : Type lzero where
  constructor lift
  field
    lower : ⌞ 0 <? j .lower ⌟

lt-nat→is-suc : (j : Fin n) → 0 <n j .lower → is-suc j
lt-nat→is-suc j p = lift $ to-prim-< p

not-suc→zero : {j : Fin (suc n)} → ¬ (is-suc j) → j ≡ fzero
not-suc→zero {j = fzero} ns = refl
not-suc→zero {j = fin (suc j)} ns = absurd $ ns $ lift oh

is-monotone : (Fin n → Fin m) → Type lzero
is-monotone f = ∀ i j → (i ≤ j) → (f i ≤ f j)

is-strict-monotone : (Fin n → Fin m) → Type lzero
is-strict-monotone f = ∀ i j → (i < j) → (f i < f j)

strict-monotone→monotone : (f : Fin n → Fin m) → is-strict-monotone f → is-monotone f
strict-monotone→monotone f sm j k le with ≤-strengthen le
... | inl eq = ≤-refl' $ ap (lower ∘ f) $ fin-ap eq
... | inr lt = <-weaken $ sm _ _ lt


injective→strict-monotone : (f : Fin n → Fin m) → injective f → is-monotone f → is-strict-monotone f
injective→strict-monotone {n = n} f inj m i j lt = <-from-≤ p $ m i j $ <-weaken lt
  where
    p : f i .lower ≠ f j .lower
    p eq = <-not-equal lt $ ap lower $ inj $ fin-ap eq

iso+monotone→strict-monotone : (f : Fin n → Fin m) → is-iso f → is-monotone f → is-strict-monotone f
iso+monotone→strict-monotone f i mon = injective→strict-monotone f (right-inverse→injective i.from i.linv) mon
  where module i = is-iso i

strict-monotone→suc-is-suc : (f : Fin (suc n) → Fin m) → is-strict-monotone f → ∀ j → is-suc (f (fsuc j))
strict-monotone→suc-is-suc f sm j = lift $ to-prim-< $ ≤<-trans 0≤x $ sm fzero (fsuc j) (s≤s 0≤x)

strict-monotone→is-suc-is-suc : (f : Fin n → Fin m) → is-strict-monotone f → ∀ j → is-suc j → is-suc (f j)
strict-monotone→is-suc-is-suc {suc n} f sm (fin (suc j) ⦃ b ⦄) _ = strict-monotone→suc-is-suc f sm (fin j ⦃ ≤-peel b ⦄)

strict-monotone→inverse-is-strict-monotone
  : ∀ {f : Fin n → Fin m} {g : Fin m → Fin n} → is-strict-monotone f → is-right-inverse g f → is-strict-monotone g
strict-monotone→inverse-is-strict-monotone {f = f} {g} sm inv j k lt = <-from-not-≤ _ _ p
  where
    f-mono : is-monotone f
    f-mono = strict-monotone→monotone f sm

    p : ¬ (g k .lower ≤n g j .lower)
    p le = <-≤-asym ((transport (λ i → inv j (~ i) < inv k (~ i)) lt)) $ f-mono (g k) (g j) le

is-suc→fpred-inv : (j : Fin (suc (suc n))) → is-suc j → fsuc (fpred j) ≡ j
is-suc→fpred-inv (fin (suc j)) _ = refl

private
  open is-iso
  f-iso→fsuc-iso : (f : Fin (suc (suc n)) → Fin (suc (suc n))) → is-iso f → is-strict-monotone f → is-iso (fpred ∘ f ∘ fsuc)
  f-iso→fsuc-iso f f-iso sm .from = fpred ∘ f-iso .from ∘ fsuc
  f-iso→fsuc-iso f f-iso sm .rinv j =
    (fpred $ f $ fsuc $ fpred $ f-iso .from $ fsuc j)
      ≡⟨ ap (fpred ∘ f)
       $ is-suc→fpred-inv _
       $ strict-monotone→suc-is-suc (f-iso .from) (strict-monotone→inverse-is-strict-monotone {f = f} sm $ f-iso .rinv) j
      ⟩
    (fpred $ f $ f-iso .from $ fsuc j)
      ≡⟨ ap fpred $ f-iso .rinv (fsuc j) ⟩
    (fpred $ fsuc j)
      ≡⟨⟩
    j ∎
  f-iso→fsuc-iso f f-iso sm .linv j =
    (fpred $ f-iso .from $ fsuc $ fpred $ f $ fsuc j)
      ≡⟨ ap (fpred ∘ f-iso .from)
       $ is-suc→fpred-inv _
       $ strict-monotone→suc-is-suc f sm j
      ⟩
    (fpred $ f-iso .from $ f $ fsuc j)
      ≡⟨ ap fpred $ f-iso .linv (fsuc j) ⟩
    (fpred $ fsuc j)
      ≡⟨⟩
    j ∎
helper : (f : Fin n → Fin n) → is-iso f → is-strict-monotone f → ∀ j → f j ≡ j
helper {suc zero} f i sm j = is-contr→is-prop fin1-is-contr _ _
helper {suc (suc n)} f i sm j with fin-view j
... | zero =  sym (ap f fbr-zero) ∙ 0-fbr .snd
  where
    -- f is an equiv
    f-eqv : is-equiv f
    f-eqv = is-iso→is-equiv i

    -- thus we have a fibre over 0
    0-fbr : fibre f (fin 0)
    0-fbr = f-eqv .is-eqv 0 .centre

    0-not-suc : ¬ is-suc fzero
    0-not-suc ()

    -- but the fibre can't be a suc
    not-suc : ¬ is-suc (0-fbr .fst)
    not-suc hyp = 0-not-suc $ subst is-suc (0-fbr .snd) (strict-monotone→is-suc-is-suc f sm _ hyp)

    -- which means it's zero
    fbr-zero : 0-fbr .fst ≡ fzero
    fbr-zero = not-suc→zero not-suc
... | suc j =
    (f $ fsuc j)  ≡˘⟨ is-suc→fpred-inv (f $ fsuc j) $ strict-monotone→suc-is-suc f sm j ⟩
    (fsuc $ f⁻ j) ≡⟨ ap fsuc $ rec j ⟩
    fsuc j ∎
  where
    f⁻ = fpred ∘ f ∘ fsuc

    is-iso⁻ : is-iso f⁻
    is-iso⁻ = f-iso→fsuc-iso f i sm

    rec : ∀ j → f⁻ j ≡ j
    rec = helper f⁻ is-iso⁻ λ i' j' p →
      (suc $ f⁻ i' .lower) =⟨ refl ⟩
      (fsuc $ fpred $ f $ fsuc i') .lower =⟨ ap lower $ is-suc→fpred-inv (f $ fsuc i') $ strict-monotone→suc-is-suc f sm i' ⟩
      (f $ fsuc i') .lower ≤⟨ ≤-pred $ sm (fsuc i') (fsuc j') (s≤s p) ⟩
      (fpred $ f $ fsuc j') .lower =⟨ refl ⟩
      (f⁻ j' .lower) ≤∎

sm-skeletal : (f g : Fin n → Fin m) → is-iso f → is-iso g → is-strict-monotone f → is-strict-monotone g → f ≡ g
sm-skeletal {n} {m} f g f-iso = J (λ k x → statement k) suffices (Fin-injective $ f , is-iso→is-equiv f-iso) f g f-iso where

  statement : Nat → Type
  statement k = ∀ (f g : Fin n → Fin k) → is-iso f → is-iso g → is-strict-monotone f → is-strict-monotone g → f ≡ g

  suffices : statement n
  suffices f g f-iso g-iso f-sm g-sm = ext λ j → helper f f-iso f-sm j ∙ (sym $ helper g g-iso g-sm j)

mon-skeletal : (f g : Fin n → Fin m) → is-iso f → is-iso g → is-monotone f → is-monotone g → f ≡ g
mon-skeletal {n} {m} f g f-iso g-iso f-mon g-mon = sm-skeletal f g f-iso g-iso f-sm g-sm
  where
    f-sm : is-strict-monotone f
    f-sm = iso+monotone→strict-monotone f f-iso f-mon
    g-sm : is-strict-monotone g
    g-sm = iso+monotone→strict-monotone g g-iso g-mon
```
