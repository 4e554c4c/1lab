<!--
```agda
open import Cat.Prelude hiding (∣_∣)
```
-->

```agda
module Cat.Double.Base where
```

# Double categories

```agda

record DoubleCategory (ℓo ℓh ℓv ℓ□ : Level) : Type (lsuc (ℓo ⊔ ℓh ⊔ ℓv ⊔ ℓ□)) where
  no-eta-equality
  field
    Hor₀  : Precategory ℓo ℓh

  open module Hor₀ = Precategory Hor₀ renaming (Hom to Hhom; Hom-set to Hhom-set; idr to idrₕ; idl to idlₕ; assoc to assocₕ) public

  field
    Vhom : Ob → Ob → Type ℓv
    Vhom-set : (x y : Ob) → is-set (Vhom x y)

  infixr 41 _⊗_

  field
    e      : ∀ {x}     → Vhom x x
    _⊗_    : ∀ {x y z} → Vhom y z → Vhom x y → Vhom x z

  infixr 25 _∣_
  infixr 26 _⊠_


  field
    Sq : ∀ {x x' y y'} (u : Vhom x y) (f : Hhom x x') (g : Hhom y y') (v : Vhom x' y') → Type ℓ□

    _∣_ : ∀ {x x' x'' y y' y''} {f : Hhom x x'} {f' : Hhom x' x''} {g : Hhom y y'} {g' : Hhom y' y''} {u : Vhom x y} {v : Vhom x' y'} {w : Vhom x'' y''}
            (α : Sq v f' g' w) (β : Sq u f g v) → Sq u (f' ∘ f) (g' ∘ g) w

    _⊠_ : ∀ {x x' y y' z z'} {f : Hhom x x'} {g : Hhom y y'} {h : Hhom z z'} {u : Vhom x y} {v : Vhom x' y'} {u' : Vhom y z} {v' : Vhom y' z'}
            (α : Sq u' g h v') (β : Sq u f g v) → Sq (u' ⊗ u) f h (v' ⊗ v)


    -- special isocells 🌈
    id[_] : ∀ {x y} (u : Vhom x y) → Sq u id id u

    e[_] : ∀ {x x'} (f : Hhom x x') → Sq e f f e


  field
    id[_]-idl : ∀ {x x' y y'} {f : Hhom x x'} {g : Hhom y y'} (u : Vhom x y) {v : Vhom x' y'} → (α : Sq u f g v) →
               PathP (λ i → Sq u (idrₕ f i) (idrₕ g i) v)
                     (α ∣ id[ u ])
                     α

    id[_]-idr : ∀ {x x' y y'} {f : Hhom x x'} {g : Hhom y y'} {u : Vhom x y} (v : Vhom x' y') → (α : Sq u f g v) →
               PathP (λ i → Sq u (idlₕ f i) (idlₕ g i) v)
                     (id[ v ] ∣ α)
                     α


  is-special-Hiso : ∀{x y} {u : Vhom x y} {v : Vhom x y}
                    (sq₁ : Sq v id id u) (sq₂ : Sq u id id v)
                    → Type ℓ□
  is-special-Hiso {x} {y} {u} {v} sq₁ sq₂ =
    (PathP (λ i → Sq u (idrₕ id i) (idrₕ id i) u)
          (sq₁ ∣ sq₂)
          id[ u ])
    × (PathP (λ i → Sq v (idrₕ id i) (idrₕ id i) v)
          (sq₂ ∣ sq₁)
          id[ v ])
  field

    λ[_]   : ∀ {x y} (u : Vhom x y) → Sq (e ⊗ u) id id u

    λ⁻¹[_]   : ∀ {x y} (u : Vhom x y) → Sq u id id (e ⊗ u)

    λ-iso : ∀ {x y } {u : Vhom x y} → is-special-Hiso λ[ u ] λ⁻¹[ u ]
    --      PathP (λ i → Sq u (idrₕ id i) (idrₕ id i) u)
    --            (λ[ u ] ∣ λ⁻¹[ u ])
    --            id[ u ]

    ρ[_]   : ∀ {x y} (u : Vhom x y) → Sq (u ⊗ e) id id u

    ρ⁻¹[_]   : ∀ {x y} (u : Vhom x y) → Sq u id id (u ⊗ e)

    ρ-iso : ∀ {x y } {u : Vhom x y} → is-special-Hiso ρ[ u ] ρ⁻¹[ u ]
    --      PathP (λ i → Sq u (idrₕ id i) (idrₕ id i) u)
    --            (ρ[ u ] ∣ ρ⁻¹[ u ])
    --            id[ u ]

    κ[_,_,_] : ∀ {w x y z} (u : Vhom y z) (v : Vhom x y) (w : Vhom w x)
          → Sq (u ⊗ (v ⊗ w)) id id ((u ⊗ v) ⊗ w)

    κ⁻¹[_,_,_] : ∀ {w x y z} (u : Vhom y z) (v : Vhom x y) (w : Vhom w x)
          → Sq ((u ⊗ v) ⊗ w) id id (u ⊗ (v ⊗ w))

    κ-iso : ∀ {w x y z} (u : Vhom y z) (v : Vhom x y) (w : Vhom w x) →
          is-special-Hiso κ[ u , v , w ] κ⁻¹[ u , v , w ]
    --      PathP (λ i → Sq ((u ⊗ v) ⊗ w) (idrₕ id i) (idrₕ id i) ((u ⊗ v) ⊗ w))
    --            (κ[ u , v , w ] ∣ κ⁻¹[ u , v , w ])
    --            id[ (u ⊗ v) ⊗ w ]

  field
    interchange : ∀ {x x' x'' y y' y'' z z' z''}
                  {f : Hhom x x'} {g : Hhom y y'} {h : Hhom z z'}
                  {f' : Hhom x' x''} {g' : Hhom y' y''} {h' : Hhom z' z''}
                  {u : Vhom x y} {v : Vhom x' y'} {w : Vhom x'' y''}
                  {u' : Vhom y z} {v' : Vhom y' z'} {w' : Vhom y'' z''}
                  (α : Sq u f g v)   (β : Sq v f' g' w)
                  (δ : Sq u' g h v') (γ : Sq v' g' h' w') →
                  (γ ∣ δ) ⊠ (β ∣ α) ≡ (γ ⊠ β) ∣ (δ ⊠ α)

    e∣e : ∀ {x x' x''} {f : Hhom x x'} {f' : Hhom x' x''} → e[ f' ] ∣ e[ f ] ≡ e[ f' ∘ f ]

    id⊠id : ∀ {x y z} {u : Vhom x y} {u' : Vhom y z} → id[ u' ] ⊠ id[ u ] ≡ id[ u' ⊗ u ]

    id[e]≡e[id] : ∀ (x : Ob) → id[ e {x} ] ≡ e[ id {x} ]

    --  x --id-→ x     x --id-→ x --id-→ x
    --  |        |     |        |        |
    --  u        u     u        u  [idᵥ] |
    --  ↓        ↓     ↓        ↓        |
    --  y  [λᵤ]  y     y        u --id-→ u
    --  |        |     |        |        |
    --  e        |  =  e [κᵥₑᵤ] e        |
    --  ↓        |     ↓        ↓        ↓
    --  y --id-→ v     y        y  [ρᵤ]  y
    --  |        |     |        |        |
    --  ∨  [idᵥ] |     v        v        v
    --  ↓        ↓     ↓        ↓        ↓
    --  z --id-→ z     z --id-→ z --id-→ z

    triangle : ∀ {x y z} {u : Vhom x y} {v : Vhom y z}
          → PathP (λ i → Sq (v ⊗ (e ⊗ u)) (idrₕ id i) (idrₕ id i) (v ⊗ u))
                  (ρ[ v ] ⊠ id[ u ] ∣ κ[ v , e , u ])
                  (id[ v ] ⊠ λ[ u ])

    pentagon : ∀ {a b c d e } {t : Vhom d e} {u : Vhom c d} {v : Vhom b c} {w : Vhom a b}
          → PathP (λ i → Sq  (t ⊗ u ⊗ v ⊗ w) (id ∘ idrₕ id i) (id ∘ idrₕ id i) (((t ⊗ u) ⊗ v) ⊗ w))
                  (κ[ t , u , v ] ⊠ id[ w ] ∣ κ[ t , u ⊗ v , w ] ∣ id[ t ] ⊠ κ[ u , v , w ])
                  (κ[ t ⊗ u , v , w ] ∣ κ[ t , u , v ⊗ w ])

open DoubleCategory using (Hor₀) public

{-
module _ {o ℓh ℓv ℓ□ : Level} (ℂ : DoubleCategory o ℓh ℓv ℓ□) where
  private
    open module ℂ = DoubleCategory ℂ

  module _ {x y : ℂ.Ob} {u : Vhom x y} where
    private
      initial-sq = λ⁻¹[ u ] ∣ λ[ u ]
      sq₂ = λ⁻¹[ u ] ∣ id[ u ] ∣ λ[ u ]
      sq₃ = λ⁻¹[ u ] ∣ λ[ u ] ∣ λ⁻¹[ u ] ∣ λ[ u ]
    pf : is-special-Hiso λ⁻¹[ u ] λ[ u ]
    pf = {! !}
-}


module _ {o ℓh ℓv ℓ□ : Level} (ℂ : DoubleCategory o ℓh ℓv ℓ□) where
  private
    open module ℂ = DoubleCategory ℂ
    foo : ∀ {x} → idrₕ (id {x}) ≡ idlₕ id
    foo = prop!

  infixl 60 _^Hop

  _^Hop : DoubleCategory o ℓh ℓv ℓ□
  (_^Hop) .Hor₀ = (Hor₀ ℂ) ^op
  (_^Hop) .Vhom = Vhom
  (_^Hop) .Vhom-set = Vhom-set
  (_^Hop) .e = e
  (_^Hop) ._⊗_ = _⊗_
  (_^Hop) .Sq u f g w = Sq w f g u
  (_^Hop) ._∣_  α β = β ∣ α
  (_^Hop) .id[_]  f = id[ f ]
  (_^Hop) .id[_]-idl u α = id[ u ]-idr α
  (_^Hop) .id[_]-idr u α = id[ u ]-idl α
  (_^Hop) .e[_]  f = e[ f ]
  (_^Hop) .λ[_]   f = λ⁻¹[ f ]
  (_^Hop) .λ⁻¹[_] f = λ[ f ]
  (_^Hop) .λ-iso {x} {y} {u} .fst i = transp (λ j → Sq u (foo {x} j i) (foo {y} j i) u) (i ∨ ~ i) (λ-iso {u = u} .fst i)
  (_^Hop) .λ-iso {x} {y} {u} .snd i = transp (λ j → Sq (e ⊗ u) (foo {x} j i) (foo {y} j i) (e ⊗ u)) (i ∨ ~ i) (λ-iso {u = u} .snd i)
  (_^Hop) ._⊠_  α β = α ⊠ β
  (_^Hop) .ρ[_]   f = ρ⁻¹[ f ]
  (_^Hop) .ρ⁻¹[_] f = ρ[ f ]
  (_^Hop) .ρ-iso {x} {y} {u} .fst i = transp (λ j → Sq u (foo {x} j i) (foo {y} j i) u) (i ∨ ~ i) (ρ-iso {u = u} .fst i)
  (_^Hop) .ρ-iso {x} {y} {u} .snd i = transp (λ j → Sq (u ⊗ e) (foo {x} j i) (foo {y} j i) (u ⊗ e)) (i ∨ ~ i) (ρ-iso {u = u} .snd i)
  (_^Hop) .κ[_,_,_] u v w = κ⁻¹[ u , v , w ]
  (_^Hop) .κ⁻¹[_,_,_] u v w = κ[ u , v , w ]
  (_^Hop) .κ-iso {a} {b} {c} {d} u v w .fst i = transp (λ j → Sq ((u ⊗ v) ⊗ w) (foo {a} j i) (foo {d} j i) ((u ⊗ v) ⊗ w)) (i ∨ ~ i) (κ-iso u v w .fst i)
  (_^Hop) .κ-iso {a} {b} {c} {d} u v w .snd i = transp (λ j → Sq (u ⊗ v ⊗ w) (foo {a} j i) (foo {d} j i) (u ⊗ v ⊗ w)) (i ∨ ~ i) (κ-iso u v w .snd i)
  (_^Hop) .e∣e = e∣e
  (_^Hop) .id⊠id = id⊠id
  (_^Hop) .id[e]≡e[id] = id[e]≡e[id]
  (_^Hop) .interchange α β δ γ = interchange β α γ δ
  (_^Hop) .triangle = {! !}
  (_^Hop) .pentagon = {! !}

{-

instance
  Underlying-DoubleCategory : ∀ {o ℓh ℓv ℓ□} → Underlying (DoubleCategory o ℓh ℓv ℓ□)
  Underlying-DoubleCategory = record { ⌞_⌟ = DoubleCategory.Ob }

record DoubleFunctor (ℓo ℓh ℓv ℓ□ ℓo' ℓh' ℓv' ℓ□' : Level)
    (ℂ : DoubleCategory ℓo ℓh ℓv ℓ□ )
    (𝔻 : DoubleCategory ℓo' ℓh' ℓv' ℓ□')
  : Type (ℓo ⊔ ℓh ⊔ ℓv ⊔ ℓ□ ⊔ ℓo' ⊔ ℓh' ⊔ ℓv' ⊔ ℓ□')
  where
  no-eta-equality

  private
    module ℂ = DoubleCategory ℂ
    module 𝔻 = DoubleCategory 𝔻

  field
    F-Hor₀ : Functor (Hor₀ ℂ) (Hor₀ 𝔻)

  open module Fₕ = Functor F-Hor₀ renaming (F₁ to Fₕ) public

  field
    Fᵥ : ∀ {x y} → ℂ.Vhom x y → 𝔻.Vhom (F₀ x) (F₀ y)
    F□ : ∀ {x x' y y'} {f : ℂ.Hhom x x'} {g : ℂ.Hhom y y'} {u : ℂ.Vhom x y} {v : ℂ.Vhom x' y'}
            (α : ℂ.Sq u f g v) → 𝔻.Sq (Fᵥ u) (Fₕ f) (Fₕ g) (Fᵥ v)

  field
    F-e : ∀ {x} → Fᵥ (ℂ.e {x}) ≡ 𝔻.e
    F-⊗ : ∀ {x y z} (v : ℂ.Vhom y z) (u : ℂ.Vhom x y)
        → Fᵥ (v ℂ.⊗ u) ≡ Fᵥ v 𝔻.⊗ Fᵥ u

  -- oopsie woopsie here come the PathPs
  -- transport is necessary in both directions, or only in one direction for a weak double category
  field
    F-id[_] : ∀ {x y} (u : ℂ.Vhom x y) →
      PathP (λ i → 𝔻.Sq (Fᵥ u) (F-id i) (F-id i) (Fᵥ u))
            (F□ ℂ.id[ u ])
            𝔻.id[ Fᵥ u ]

    F-e[_] : ∀ {x x'} (f : ℂ.Hhom x x') →
      PathP (λ i → 𝔻.Sq (F-e i) (Fₕ f) (Fₕ f) (F-e i))
            (F□ ℂ.e[ f ])
            𝔻.e[ Fₕ f ]
-}
```
