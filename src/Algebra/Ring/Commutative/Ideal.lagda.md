<!--
```agda
open import Algebra.Ring.Module.Action
open import Algebra.Ring.Commutative
open import Algebra.Group.Subgroup
open import Algebra.Ring.Module
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring
open import Data.Int

open import Cat.Displayed.Univalence.Thin
open import Cat.Displayed.Total
open import Cat.Prelude hiding (_*_) renaming (_+_ to _+ℕ_; _-_ to _-ℕ_)

open import Data.Power
open import Algebra.Ring.Localisation

open import Algebra.Ring.Quotient
import Algebra.Ring.Commutative.Reasoning as CRingr
import Algebra.Ring.Ideal as NCideal
```
-->

```agda
module Algebra.Ring.Commutative.Ideal where
```

<!--
```agda
private
  variable o : Level

module _ {ℓ} {R : CRing ℓ} where

  open CRingr R
  open NCideal
  open Ideal
  --open RQ ring
  --open Frac R
```
-->

# Ideals in commutative rings

```agda
```

### Principal ideals
```agda
  Principal : ⌞ R ⌟ → Ideal ring
  Principal a = record { has-is-ideal = principal-ideal ring a central }
```

## Prime ideals

```agda
  record is-prime (𝔞 : ℙ ⌞ R ⌟) (ideal : is-ideal ring 𝔞) : Type (lsuc ℓ) where
    no-eta-equality
    field
      absorbs : ∀ {a b} → a * b ∈ 𝔞 → (a ∈ 𝔞) × (b ∈ 𝔞)
      not-id  : 1r ∉ 𝔞

  infix 3 Principal
  syntax Principal {R = R} I  = 〔 I 〕[ R ]
```


## Kernel ideals

```agda

```

## Radicals

```agda
  √_ : (I : Ideal ring) → Ideal ring
  (√ I) = nil where
    module I = Ideal I
    open represents-subgroup
    open is-ideal
    nil : Ideal ring
    nil .𝔞 x = ∃Ω Nat λ n → I .𝔞 $ (x ^ᴿ n)
    nil .has-is-ideal .has-rep-subgroup .has-unit =
      inc ( 1 , subst (_∈ I .𝔞) (sym m.pow-1-eq) I.has-unit)
    nil .has-is-ideal .has-rep-subgroup .has-⋆ {x} {y} = elim! λ n p m q →
      -- TODO
      inc (m +ℕ n -ℕ 1 , {! !})
    --has-unit = ?
  --.𝔞 x = ∃Ω Nat λ n → I .𝔞 $ (x ^ᴿ n)
  --(√ I) .has-is-ideal .has-rep-subgroup .has-unit =
  --(√ I) .has-is-ideal .is-ideal.has-*ₗ = {! !}
  --(√ I) .has-is-ideal .is-ideal.has-*ᵣ = {! !}
```


### Prime ideals as "Generalized points"


```agda

the : (A : Type o) → A → A
the _ x = x

open CRingr
open NCideal
open Ideal

_ : Ideal (ring ℤ-comm)
_ = 〔 3 〕[ ℤ-comm ]
_ : ⌞ (ring ℤ-comm) /ᴿ 〔 3 〕[ ℤ-comm ] ⌟
_ = (the Int 2) · 〔 3 〕[ ℤ-comm ]
```
