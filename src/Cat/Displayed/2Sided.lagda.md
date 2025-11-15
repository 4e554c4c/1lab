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
```
-->

```agda
module Cat.Displayed.2Sided where
```

# Two-sided displayed categories {defines=two-sided-displayed-category}


```agda
private variable
  o ℓ : Level
record Displayed  (B : Precategory o ℓ) (C : Precategory o ℓ)
                 (o' ℓ' : Level) : Type (o ⊔ ℓ ⊔ lsuc o' ⊔ lsuc ℓ') where
  no-eta-equality
  private
    module B = Precategory B
    module C = Precategory C
  field
    Ob[_,_] : B.Ob → C.Ob → Type o'
    Hom[_,_] : ∀ {a b n m} → B.Hom a b → C.Hom n m → Ob[ a , n ] → Ob[ b , m ] → Type ℓ'
    Hom[_,_]-set : ∀ {a b n m} (f : B.Hom a b) (u : C.Hom n m) (x : Ob[ a , n ]) (y : Ob[ b , m ])
               → is-set (Hom[ f , u ] x y)
    id' : ∀ {a u} {x : Ob[ a , u ]} → Hom[ B.id , C.id ] x x
    _∘'_ : ∀ {a b c n m k x y z} {f : B.Hom b c} {g : B.Hom a b} {u : C.Hom m k} {v : C.Hom n m}
         → Hom[ f , u ] y z → Hom[ g , v ] x y → Hom[ f B.∘ g , u C.∘ v ] x z
  infixr 40 _∘'_

  _≡[_,_]_ : ∀ {a b n m x y} {f g : B.Hom a b} {u v : C.Hom n m} → Hom[ f , u ] x y → f ≡ g → u ≡ v → Hom[ g , v ] x y → Type ℓ'
  _≡[_,_]_ {a} {b} {n} {m} {x} {y} f' p q g' = PathP (λ i → Hom[ p i , q i ] x y) f' g'

  infix 30 _≡[_,_]_

  field
    idr' : ∀ {a b n m x y} {f : B.Hom a b} {u : C.Hom n m} (f' : Hom[ f , u ] x y) → f' ∘' id' ≡[ B.idr f , C.idr u ] f'
    idl' : ∀ {a b n m x y} {f : B.Hom a b} {u : C.Hom n m} (f' : Hom[ f , u ] x y) → id' ∘' f' ≡[ B.idl f , C.idl u ] f'
    assoc' : ∀ {a b c d n m k l x y z zz}
      {f : B.Hom c d} {g : B.Hom b c} {h : B.Hom a b}
      {u : C.Hom k l} {v : C.Hom m k} {w : C.Hom n m} →
      (f' : Hom[ f , u ] z zz) →
      (g' : Hom[ g , v ] y z) →
      (h' : Hom[ h , w ] x y) →
      f' ∘' (g' ∘' h') ≡[ B.assoc f g h , C.assoc u v w  ] (f' ∘' g') ∘' h'
  field
    hom[_,_]
      : ∀ {a b n m x y} {f g : B.Hom a b} {u v : C.Hom n m} (p : f ≡ g) (q : u ≡ v)
      (f' : Hom[ f , u ] x y)
      → Hom[ g , v ] x y
    coh[_,_]
      : ∀ {a b n m x y} {f g : B.Hom a b} {u v : C.Hom n m} (p : f ≡ g) (q : u ≡ v)
      (f' : Hom[ f , u ] x y)
      → f' ≡[ p , q ] hom[ p , q ] f'

  private variable
    a b c : B.Ob
    n m k : C.Ob
    f g h : B.Hom a b
    u v w : C.Hom n m
    x y z : Ob[ a , n ]
    f' g' h' : Hom[ f , u ] x y

  _∙[]_ : {p : f ≡ g} {q : g ≡ h} {p' : u ≡ v} {q' : v ≡ w}
        → {f' : Hom[ f , u ] x y} {g' : Hom[ g , v ] x y} {h' : Hom[ h , w ] x y}
        → f' ≡[ p , p' ] g'
        → g' ≡[ q , q' ] h'
        → f' ≡[ p ∙ q , p' ∙ q' ] h'
  _∙[]_ {x = x} {y = y}{p = p} {q = q} {p'} {q'}  {f' = f'} π ρ i =
    comp (λ j → Hom[ ∙-filler p q j i , ∙-filler p' q' j i ] x  y ) (∂ i) λ where
      j (i = i0) → f'
      j (i = i1) → ρ j
      j (j = i0) → π i

  ∙[-]-syntax : ∀ (p : f ≡ g) {p' : g ≡ h} (q : u ≡ v) {q' : v ≡ w}
        --→ {f' : Hom[ f ] x y}
        --  {g' : Hom[ g ] x y}
        --  {h' : Hom[ h ] x y}
        → f' ≡[ p , q ] g' → g' ≡[ p' , q' ] h' → f' ≡[ p ∙ p' , q ∙ q' ] h'
  ∙[-]-syntax p q π ρ = π ∙[] ρ

  ≡[]⟨⟩-syntax : ∀ {p : f ≡ g} {p' : g ≡ h} {q : u ≡ v} {q' : v ≡ w}
               → (f' : Hom[ f ] x y) {g' : Hom[ g ] x y} {h' : Hom[ h ] x y}
               → g' ≡[ q ] h' → f' ≡[ p ] g' → f' ≡[ p ∙ q ] h'
  ≡[]⟨⟩-syntax f' q' p' = p' ∙[] q'

  syntax ∙[-]-syntax p p' q' = p' ∙[ p ] q'
```

<!--
```agda
{-

  ≡[-]⟨⟩-syntax : ∀ {a b x y} {f g h : Hom a b} (p : f ≡ g) {q : g ≡ h}
               → (f' : Hom[ f ] x y) {g' : Hom[ g ] x y} {h' : Hom[ h ] x y}
               → g' ≡[ q ] h' → f' ≡[ p ] g' → f' ≡[ p ∙ q ] h'
  ≡[-]⟨⟩-syntax f' p q' p' = p' ∙[] q'

  _≡[]˘⟨_⟩_ : ∀ {a b x y} {f g h : Hom a b} {p : g ≡ f} {q : g ≡ h}
            → (f' : Hom[ f ] x y) {g' : Hom[ g ] x y} {h' : Hom[ h ] x y}
            → g' ≡[ p ] f' → g' ≡[ q ] h' → f' ≡[ sym p ∙ q ] h'
  f' ≡[]˘⟨ p' ⟩ q' = symP p' ∙[] q'

  syntax ≡[]⟨⟩-syntax f' q' p' = f' ≡[]⟨ p' ⟩ q'
  syntax ≡[-]⟨⟩-syntax p f' q' p' = f' ≡[ p ]⟨ p' ⟩ q'

  infixr 30 _∙[]_ ∙[-]-syntax
  infixr 2 ≡[]⟨⟩-syntax ≡[-]⟨⟩-syntax _≡[]˘⟨_⟩_

{-# INLINE Displayed.constructor #-}


private
  Hom[]-set
    : ∀ {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') {x y} {f : B .Precategory.Hom x y} {x' y'}
    → is-set (E .Displayed.Hom[_] f x' y')
  Hom[]-set E = E .Displayed.Hom[_]-set _ _ _

instance
  Hom[]-hlevel-proj : hlevel-projection (quote Displayed.Hom[_])
  Hom[]-hlevel-proj .has-level   = quote Hom[]-set
  Hom[]-hlevel-proj .get-level _ = pure (lit (nat 2))
  Hom[]-hlevel-proj .get-argument (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ arg _ t ∷ _) =
    pure t
  {-# CATCHALL #-}
  Hom[]-hlevel-proj .get-argument _ =
    typeError []

  Funlike-Displayed : ∀ {o ℓ o' ℓ'} {B : Precategory o ℓ} → Funlike (Displayed B o' ℓ') ⌞ B ⌟ λ _ → Type o'
  Funlike-Displayed = record { _·_ = Displayed.Ob[_] }

module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} {E : Displayed B o' ℓ'} where
  _ : ∀ {x y} {f : B .Precategory.Hom x y} {x' y'} → is-set (E .Displayed.Hom[_] f x' y')
  _ = hlevel 2
-}
```
-->
