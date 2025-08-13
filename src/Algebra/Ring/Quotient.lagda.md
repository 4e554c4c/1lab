<!--
```agda
open import Algebra.Group.Cat.Base
open import Algebra.Group.Subgroup
open import Algebra.Ring.Ideal
open import Algebra.Group
open import Algebra.Ring

open import Cat.Prelude hiding (_*_ ; _+_ ; _-_)

open import Data.Power
open import Data.Dec

import Algebra.Ring.Reasoning as Kit
```
-->

```agda
module Algebra.Ring.Quotient where
```

# Quotient rings

Let $R$ be a [[ring]] and $I \sube R$ be an ideal. Because rings have an
underlying [[abelian group]], the ideal $I \sube R$ determines a normal
subgroup $I$ of $R$'s additive group, so that we may form the quotient
group $R/I$. And since ideals are closed under multiplication^[recall
that all our rings are commutative, so they're closed under
multiplication by a constant on either side], we can extend $R$'s
multiplication to a multiplication operation on $R/I$ in a canonical
way! In that case, we refer to $R/I$ as a **quotient ring**.

[quotient group]: Algebra.Group.Subgroup.html#representing-kernels

<!--
```agda
module _ {ℓ} (R : Ring ℓ) (I : Ideal R)  where
  private module I = Ideal I
  open Ring-on (R .snd)
  private module R = Kit R
```
-->


Really, the bulk of the construction has already been done (in the
section about quotient groups), so all that remains is the following
construction: We want to show that $xy$ is invariant under equivalence
for both $x$ and $y$ (and we may treat them separately for
comprehensibility's sake).

<!--
```agda
  private
    quot-grp : Group _
    quot-grp = R.additive-group /ᴳ I.ideal→normal
    module R/I = Group-on (quot-grp .snd) hiding (magma-hlevel)
```
-->

```agda
    quot-mul : ⌞ quot-grp ⌟ → ⌞ quot-grp ⌟ → ⌞ quot-grp ⌟
    quot-mul =
      Coeq-rec₂ squash (λ x y → inc (x R.* y))
        (λ a (_ , _ , r) → p1 a r)
        (λ a (_ , _ , r) → p2 a r)
      where
```

On one side, we must show that $[ax] = [ay]$ supposing that $[x] = [y]$,
i.e. that $(x - y) \in I$. But since $I$ is an ideal, we have $(ax - ay)
\in I$, thus $[ax] = [ay]$. And on the other side, we have the same
thing: Since $(x - y) \in I$, also $(xa - ya) \in I$, so $[xa] = [ya]$.

```agda
      p1 : ∀ a {x y} (r : (x R.- y) ∈ I) → inc (x R.* a) ≡ inc (y R.* a)
      p1 a {x} {y} x-y∈I = quot $ subst (_∈ I)
        (R.*-distribr ∙ ap (x R.* a R.+_) R.*-negatel)
        (I.has-*ᵣ a x-y∈I)

      p2 : ∀ a {x y} (r : (x R.- y) ∈ I) → inc (a R.* x) ≡ inc (a R.* y)
      p2 a {x} {y} x-y∈I = quot $ subst (_∈ I)
        (R.*-distribl ∙ ap (a R.* x R.+_) R.*-negater)
        (I.has-*ₗ a x-y∈I)
```

<details>
<summary>Showing that this extends to a ring structure on $R/I$ is annoying, but
not non-trivial, so we keep in this `<details>`{.Agda} fold. Most of the proof is appealing to the elimination principle(s) for
quotients into propositions, then applying $R$'s laws.</summary>

```agda
  open make-ring
  make-R/I : make-ring ⌞ quot-grp ⌟
  make-R/I .ring-is-set = squash
  make-R/I .0R = inc 0r
  make-R/I ._+_ = R/I._⋆_
  make-R/I .-_ = R/I.inverse
  make-R/I .+-idl x = R/I.idl
  make-R/I .+-invr x = R/I.inverser {x}
  make-R/I .+-assoc x y z = R/I.associative {x} {y} {z}
  make-R/I .1R = inc R.1r
  make-R/I ._*_ = quot-mul
  make-R/I .+-comm = elim! λ x y → ap Coeq.inc R.+-commutes
  make-R/I .*-idl = elim! λ x → ap Coeq.inc R.*-idl
  make-R/I .*-idr = elim! λ x → ap Coeq.inc R.*-idr
  make-R/I .*-assoc = elim! λ x y z → ap Coeq.inc R.*-associative
  make-R/I .*-distribl = elim! λ x y z → ap Coeq.inc R.*-distribl
  make-R/I .*-distribr = elim! λ x y z → ap Coeq.inc R.*-distribr
```

</details>

```agda
  _/ᴿ_ : Ring ℓ
  _/ᴿ_ .fst = el! _
  _/ᴿ_ .snd = to-ring-on make-R/I
```

```agda
  open is-ring-hom
  inclᴿ : Rings.Hom R _/ᴿ_
  inclᴿ .fst = inc
  inclᴿ .snd .pres-id = refl
  inclᴿ .snd .pres-+ _ _ = refl
  inclᴿ .snd .pres-* _ _ = refl

  /ᴿ-rec
    : ∀ {ℓ'} (B : Ring ℓ') (f : ⌞ R ⌟ → ⌞ B ⌟)
    → ({x y : ⌞ R ⌟} → (x R.- y) ∈ I → f x ≡ f y)
    → ⌞ _/ᴿ_ ⌟ → ⌞ B ⌟
  /ᴿ-rec B f h (inc x) = f x
  /ᴿ-rec B f h (glue (a , b , m) i) = h m i
  /ᴿ-rec B f h (squash x y p q i j) = hlevel {T = ⌞ B ⌟} 2 (go x) (go y) (λ i → go (p i)) (λ i → go (q i)) i j -- Quot-elim (λ _ → hlevel 2) f λ x y → h {x} {y}
    where go = /ᴿ-rec B f h

  abstract
    /ᴿ-rec-is-hom
      : ∀ {ℓ'} {B : Ring ℓ'} {f : ⌞ R ⌟ → ⌞ B ⌟} {h : {x y : ⌞ R ⌟} → (x R.- y) ∈ I → f x ≡ f y}
      → is-ring-hom (R .snd) (B .snd) f
      → is-ring-hom (_/ᴿ_ .snd) (B .snd) (/ᴿ-rec B f h)
    /ᴿ-rec-is-hom {f = f} {h = h} rh .pres-id = rh .pres-id
    /ᴿ-rec-is-hom {f = f} {h = h} rh .pres-+ = elim! (rh .pres-+)
    /ᴿ-rec-is-hom {f = f} {h = h} rh .pres-* = elim! (rh .pres-*)
```

As a quick aside, if $I$ is a complemented ideal (equivalently: a
decidable ideal), and $R$ is a discrete ring, then the quotient ring is
also discrete. This is a specialisation of a general result about
decidable quotient sets, but we mention it here regardless:

```agda
  Discrete-ring-quotient : (∀ x → Dec (x ∈ I)) → Discrete ⌞ _/ᴿ_  ⌟
  Discrete-ring-quotient dec∈I = Discrete-quotient
    (normal-subgroup→congruence R.additive-group I.ideal→normal)
    (λ x y → dec∈I (x R.- y))

instance
  Funlike-Ring : ∀ {ℓ} {R : Ring ℓ} → Funlike ⌞ R ⌟ (Ideal R) (λ I → ⌞ R /ᴿ I  ⌟)
  Funlike-Ring {R = R} = record { _·_ = λ x I → inclᴿ R I · x  }

/ᴿ-universal
  : ∀ {ℓ} {R B : Ring ℓ} {I : Ideal R} (f : Rings.Hom R B) (let open Ring-on (R .snd))
  → ({x y : ⌞ R ⌟} → (x - y) ∈ I → f · x ≡ f · y)
  → Rings.Hom (R /ᴿ I) B
/ᴿ-universal {R = R} {B} {I} f h .fst = /ᴿ-rec R I B (apply f) h
/ᴿ-universal {R = R} {B} {I} f h .snd = /ᴿ-rec-is-hom R I (f .snd)
```
