<!--
```agda
--open import 1Lab.Reflection.HLevel
--open import 1Lab.HLevel.Closure
--open import 1Lab.Reflection
--open import 1Lab.Path
--open import 1Lab.Type hiding (id ; _∘_)
--open import Data.Fin.Product
--open import Data.Fin.Base
--open import Data.List.Properties
--open import Data.Vec.Base
open import 1Lab.Underlying
open import 1Lab.Prelude hiding (Σ-syntax)
open import 1Lab.HLevel

open import Data.Fin.Finite

module Test {o ℓ : Level} where
private variable
  k : Level

record fin-Type k : Type (lsuc k) where
  no-eta-equality
  constructor el
  field
    ∣_∣ꟳ     : Type k
    ⦃ is-fin ⦄ : Finite ∣_∣ꟳ

  infix 100 ∣_∣ꟳ
  instance
    Finite-fin-Type : Finite ∣_∣ꟳ
    Finite-fin-Type = is-fin


open fin-Type public

eln! : ∀ {ℓ} (A : Type ℓ) ⦃ hl : Finite A ⦄ → fin-Type ℓ
eln! A .∣_∣ꟳ = A
eln! A ⦃ hl ⦄ .is-fin = hl

open Underlying using (ℓ-underlying)

instance
  Underlying-fin-Type : ∀ {k} → Underlying (fin-Type k)
  Underlying-fin-Type {k} .ℓ-underlying = k
  Underlying-fin-Type .⌞_⌟ x = ∣ x ∣ꟳ

module _ {I : fin-Type ℓ} {J : ⌞ I ⌟ → fin-Type ℓ} where
  Σfin : fin-Type ℓ
  -- this worksn't
  --Σfin = eln! (Σ[ i ∈ I ] ⌞ J i ⌟)

  --{-# INCOHERENT Finite-fin-Underlying #-}
  --{-# INCOHERENT Underlying-fin-Type #-}

--  instance
--    H-Level-n-type : ∀ {k} → H-Level ∣_∣ (n + k)
--    H-Level-n-type = basic-instance n is-tr

{-
record MultiCategory (o ℓ e ı : Level) : Type (lsuc (o ⊔ ℓ ⊔ e ⊔ ı)) where
  field
    Obj : Type o
    Hom : {I : fin-Type ı} → (⌞ I ⌟ → Obj) → Obj → Type ℓ
    _⨟_ : {I : fin-Type ı} {aₙ : ⌞ I ⌟ → Obj} {a : Obj} {J : ⌞ I ⌟ → fin-Type ı}
          {v : (i : ⌞ I ⌟ ) → ⌞ J i ⌟ → Obj} →
          ((i : ⌞ I ⌟) → Hom {J i} (v i) (aₙ i)) → Hom {I} aₙ a → Hom {eln! (Σ[ i ∈ I ] ⌞ J i ⌟)} (uncurry v) a


-- the ı level is for the 'index' (and to not steal 'i')

-- The important part is that in _∘_, there is no flattening of the
-- index set. But also _≈[_]_ builds in an explicit equivalence
-- that allows one to properly re-index things. The classical view
-- of MultiCategory sweeps all of that under the rug, which gives
-- Agda conniptions (and rightfully so). The advantage of doing it
-- this way makes it clear that the 3 laws are based on the underlying
-- 3 laws that hold for (dependent!) product.

-- The upshot is that this version of MultiCategory makes no finiteness
-- assumption whatsoever.  The index sets involved could be huge,
-- without any issues.

-- Note that this still isn't Symmetric Multicategory. The renaming that
-- happens on indices say nothing about the relation to the contents
-- of the other Hom set.

-- any point can be lifted to a function from ⊤
pointed : {s t : Level} {S : Set s} (x : S) → ⊤ {t} → S
pointed x _ = x

-- the standard library doesn't seem to have the 'right' version of these.
⊤×K↔K : {t k : Level} {K : Set k} → (⊤ {t} × K) ↔ K
⊤×K↔K = mk↔ₛ′ proj₂ (tt ,_) (λ _ → refl) λ _ → refl

K×⊤↔K : {t k : Level} {K : Set k} → (K × ⊤ {t}) ↔ K
K×⊤↔K = mk↔ₛ′ proj₁ (_, tt) (λ _ → refl) λ _ → refl

⊤×⊤↔⊤ : {t : Level} → (⊤ {t} × ⊤) ↔ ⊤
⊤×⊤↔⊤ = mk↔ₛ′ proj₁ (λ x → x , x) (λ _ → refl) λ _ → refl

Σ-assoc : {a b c : Level} {I : Set a} {J : I → Set b} {K : Σ I J → Set c} →
  Σ (Σ I J) K ↔ Σ I (λ i → Σ (J i) (curry K i))
Σ-assoc {I = I} {J} {K} = mk↔ₛ′ g f (λ _ → refl) λ _ → refl
  where
  f : Σ I (λ i → Σ (J i) (λ j → K (i , j))) → Σ (Σ I J) K
  f (i , j , k) = (i , j) , k
  g : Σ (Σ I J) K → Σ I (λ i → Σ (J i) (λ j → K (i , j)))
  g ((i , j) , k) = i , j , k

-- the ı level is for the 'index' (and to not steal 'i')

-- The important part is that in _∘_, there is no flattening of the
-- index set. But also _≈[_]_ builds in an explicit equivalence
-- that allows one to properly re-index things. The classical view
-- of MultiCategory sweeps all of that under the rug, which gives
-- Agda conniptions (and rightfully so). The advantage of doing it
-- this way makes it clear that the 3 laws are based on the underlying
-- 3 laws that hold for (dependent!) product.

-- The upshot is that this version of MultiCategory makes no finiteness
-- assumption whatsoever.  The index sets involved could be huge,
-- without any issues.

-- Note that this still isn't Symmetric Multicategory. The renaming that
-- happens on indices say nothing about the relation to the contents
-- of the other Hom set.
record MultiCategory (o ℓ e ı : Level) : Set (suc (o ⊔ ℓ ⊔ e ⊔ ı)) where
  infix  4 _≈[_]_
  infixr 9 _∘_

  field
    Obj : Set o
    Hom : {I : Set ı} → (I → Obj) → Obj → Set ℓ
    id : (o : Obj) → Hom {⊤} (pointed o) o
    _∘_ : {I : Set ı} {aₙ : I → Obj} {a : Obj} {J : I → Set ı}
          {v : (i : I) → J i → Obj} →
          Hom {I} aₙ a → ((i : I) → Hom (v i) (aₙ i)) → Hom {Σ I J} (uncurry v) a
    _≈[_]_ : {I J : Set ı} {aₙ : I → Obj} {a : Obj} →
          Hom {I} aₙ a → (σ : I ↔ J) → Hom {J} (aₙ ● Inverse.from σ) a → Set e

    identityˡ : {K : Set ı} {aₖ : K → Obj} {a : Obj} {f : Hom aₖ a} →
              id a ∘ pointed f ≈[ ⊤×K↔K ]  f
    identityʳ : {K : Set ı} {aₖ : K → Obj} {a : Obj} {f : Hom aₖ a} →
              f ∘ (id ● aₖ) ≈[ K×⊤↔K ] f

    identity² : {a : Obj} → id a ∘ pointed (id a) ≈[ ⊤×⊤↔⊤ ] id a

    assoc : -- the 3 index sets
            {I : Set ı} {J : I → Set ı} {K : Σ I J → Set ı}
            -- the 4 (increasingly indexed) objects
            {a : Obj} {aᵢ : I → Obj}
            {aᵢⱼ : (i : I) → J i → Obj}
            {aᵢⱼₖ : (h : Σ I J) → K h → Obj}
            -- the 3 Homs
            {h : Hom aᵢ a}
            {g : (i : I) → Hom (aᵢⱼ i) (aᵢ i)}
            {f : (k : Σ I J) → Hom (aᵢⱼₖ k) (uncurry aᵢⱼ k)} →
            -- and their relation under composition
            (h ∘ g) ∘ f ≈[ Σ-assoc ] h ∘ (λ i → g i ∘ curry f i)

    -- we also need that _≈[_]_ is, in an appropriate sense, an equivalence relation, which in this case
    -- means that _≈[ id↔ ]_ is.  In other words, we don't care when transport is over 'something else'.
    refl≈ : {I : Set ı} {aₙ : I → Obj} {a : Obj} →
            {h : Hom {I} aₙ a} → h ≈[ id↔ (setoid I) ] h
    sym≈ : {I : Set ı} {aₙ : I → Obj} {a : Obj} →
           {g h : Hom {I} aₙ a} → g ≈[ id↔ (setoid I) ] h → h ≈[ id↔ (setoid I) ] g
    trans≈ : {I : Set ı} {aₙ : I → Obj} {a : Obj} →
           {f g h : Hom {I} aₙ a} → f ≈[ id↔ (setoid I) ] g → g ≈[ id↔ (setoid I) ] h → f ≈[ id↔ (setoid I) ] h

    ∘-resp-≈ : {I : Set ı} {J : I → Set ı}
               {a : Obj} {aᵢ : I → Obj} {aᵢⱼ : (i : I) → J i → Obj}
               {g g′ : Hom aᵢ a} {f f′ : (i : I) → Hom (aᵢⱼ i) (aᵢ i)} →
               g ≈[ id↔ (setoid I) ] g′ → (∀ i → f i ≈[ id↔ (setoid (J i)) ] f′ i) →
               g ∘ f ≈[ id↔ (setoid (Σ I J)) ] g′ ∘ f′

-}

```

