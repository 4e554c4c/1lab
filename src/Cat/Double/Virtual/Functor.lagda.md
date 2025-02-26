<!--
```agda
open import Cat.Prelude hiding (∣_∣)
open import Cat.Double.Virtual
```
-->

```agda
module Cat.Double.Virtual.Functor {ℓo ℓt ℓl ℓ□ ℓo' ℓt' ℓl' ℓ□' : Level}
  (ℂ : VirtualDoubleCategory ℓo ℓt ℓl ℓ□) (𝔻 : VirtualDoubleCategory ℓo' ℓt' ℓl' ℓ□') where
```

# Virtual double functors

```agda
private
  module ℂ = VirtualDoubleCategory ℂ
  module 𝔻 = VirtualDoubleCategory 𝔻

record VDFData : Type (ℂ.level ⊔ 𝔻.level) where
  no-eta-equality
  field
    tight : Functor ℂ.TightCat 𝔻.TightCat
  open Functor tight renaming (F₁ to Fᵥ; ₁ to ᵥ; F-id to F-idᵥ) public

  field
    Fₕ : ∀ {x y} → x ℂ.⇸ y → F₀ x 𝔻.⇸ F₀ y

  Fₕ…ₕ : ∀ {x y} → x ℂ.⇸⋯⇸ y → F₀ x 𝔻.⇸⋯⇸ F₀ y
  Fₕ…ₕ (ℂ.[] {X = X}) = 𝔻.[]
  Fₕ…ₕ (ℂ.cons x m) = 𝔻.cons (Fₕ x) (Fₕ…ₕ m)

  F-resp-⊛ : ∀ {x y z} → (m : x ℂ.⇸⋯⇸ y) → (n : y ℂ.⇸⋯⇸ z)
           → Fₕ…ₕ (m ℂ.⊛ n) ≡ Fₕ…ₕ m 𝔻.⊛ Fₕ…ₕ n
  F-resp-⊛ ℂ.[] n = refl
  F-resp-⊛ (ℂ.cons f m) n = ap (𝔻.cons $ Fₕ f) $ F-resp-⊛ m n
```
<!--
```agda
  ₕ = Fₕ
  ₕ…ₕ = Fₕ…ₕ
```
-->
```agda
record VDFStructure (d : VDFData) : Type (ℂ.level ⊔ 𝔻.level)where
  open VDFData d public

  field
    F□ : ∀ {X X' Y Y'} {f : X ℂ.↓ X'} {m : X ℂ.⇸⋯⇸ Y} {q : X' ℂ.⇸ Y'} {g : Y ℂ.↓ Y'}
       → ℂ.┌ m ┐
           f □ g
           └ q ┘
       → 𝔻.┌  Fₕ…ₕ m  ┐
            Fᵥ f □ Fᵥ g
           └   Fₕ q   ┘
    F-id□ : ∀ {X Y} (p : X ℂ.⇸ Y)
        → PathP (λ i → 𝔻.┌ 𝔻.single (Fₕ p) ┐
                          F-idᵥ i □ F-idᵥ i
                         └       Fₕ p      ┘)
                (F□ (ℂ.id□ p)) (𝔻.id□ $ Fₕ p)
  F□⋯□ : ∀ {X X' Y Y'} {f : X ℂ.↓ X'} {m : X ℂ.⇸⋯⇸ Y} {q : X' ℂ.⇸⋯⇸ Y'} {g : Y ℂ.↓ Y'}
     → ℂ.┌  m  ┐
         f □⋯□ g
         └  q  ┘
     → 𝔻.┌    Fₕ…ₕ m    ┐
          Fᵥ f □⋯□ Fᵥ g
         └    Fₕ…ₕ q    ┘
  F□⋯□ ℂ.□[] = 𝔻.□[]
  F□⋯□ {f = f} {_} {q} {g} (ℂ.□cons {top = m} {top' = n} a 𝔞) =
    transport (λ i → 𝔻.┌ F-resp-⊛ m n (~ i) ┐
                           Fᵥ f □⋯□ Fᵥ g
                       └      Fₕ…ₕ q        ┘) $
              𝔻.□cons (F□ a) (F□⋯□ 𝔞)

record VDFLaws {d} (s : VDFStructure d) : Type (ℂ.level ⊔ 𝔻.level)where
  open VDFStructure s public
  field
    vcomp : ∀ {X X' X'' f Y Y' Y'' g q} {f' : X' ℂ.↓ X''} {g' : Y' ℂ.↓ Y''} {top : X ℂ.⇸⋯⇸ Y} {mid : X' ℂ.⇸⋯⇸ Y'}
          → (𝔞 : ℂ.┌  top  ┐
                    f □⋯□ g
                   └  mid  ┘)
          → (b : ℂ.┌  mid  ┐
                    f' □  g'
                   └   q   ┘)
          → PathP (λ i → 𝔻.┌        Fₕ…ₕ top       ┐
                            F-∘ f' f i □ F-∘ g' g i
                           └          Fₕ q         ┘)
                   (F□ $ ℂ.vcomp 𝔞 b)
                   (𝔻.vcomp (F□⋯□ 𝔞) (F□ b))


record VDFunctor : Type (ℂ.level ⊔ 𝔻.level) where
  no-eta-equality
  field
    Data : VDFData
    Struct : VDFStructure Data
    Laws : VDFLaws Struct
  open VDFLaws Laws public

```
