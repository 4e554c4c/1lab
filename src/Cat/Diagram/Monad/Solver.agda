module Cat.Diagram.Monad.Solver where

open import 1Lab.Prelude hiding (id; _∘_; refl⟩∘⟨_; _⟩∘⟨refl)
open import 1Lab.Reflection hiding (_++_)
open import Data.Id.Base

open import Cat.Base
open import Cat.Diagram.Monad

import Cat.Functor.Reasoning
import Cat.Reasoning

open import Data.List hiding (_++_)

module NbE {o h} {C : Precategory o h} {M : Functor C C} (monad : Monad-on M) where
  private
    open Cat.Reasoning C
    open Monad-on monad
    module M = Cat.Functor.Reasoning M

  data “Ob” : Type o where
    “_”  : Ob → “Ob”
    “M₀” : “Ob” → “Ob”

  sem-ob : “Ob” → Ob
  sem-ob “ X ” = X
  sem-ob (“M₀” X) = M₀ (sem-ob X)

  instance
    Brackets-“Ob” : ⟦⟧-notation “Ob”
    Brackets-“Ob” .⟦⟧-notation.lvl = o
    Brackets-“Ob” .⟦⟧-notation.Sem = Ob
    Brackets-“Ob” .⟦⟧-notation.⟦_⟧ = sem-ob

  data “Hom” : “Ob” → “Ob” → Type (o ⊔ h) where
    “M₁”  : ∀ {X Y} → “Hom” X Y → “Hom” (“M₀” X) (“M₀” Y)
    “η”   : (X : “Ob”) → “Hom” X (“M₀” X)
    “μ”   : (X : “Ob”) → “Hom” (“M₀” (“M₀” X)) (“M₀” X)
    _“∘”_ : ∀ {X Y Z} → “Hom” Y Z → “Hom” X Y → “Hom” X Z
    “id”  : ∀ {X} → “Hom” X X
    _↑    : ∀ {X Y} → Hom ⟦ X ⟧ ⟦ Y ⟧ → “Hom” X Y

  sem-hom : ∀ {X Y} → “Hom” X Y → Hom ⟦ X ⟧ ⟦ Y ⟧
  sem-hom (“M₁” f) = M₁ (sem-hom f)
  sem-hom (“η” _) = η _
  sem-hom (“μ” X) = μ _
  sem-hom (f “∘” g) = sem-hom f ∘ sem-hom g
  sem-hom “id” = id
  sem-hom (f ↑) = f

  instance
    Brackets-“Hom” : ∀ {X Y} → ⟦⟧-notation (“Hom” X Y)
    Brackets-“Hom” .⟦⟧-notation.lvl = h
    Brackets-“Hom” .⟦⟧-notation.Sem = _
    Brackets-“Hom” .⟦⟧-notation.⟦_⟧ = sem-hom

  data Frame : “Ob” → “Ob” → Type (o ⊔ h) where
    khom  : ∀ {X Y} → Hom ⟦ X ⟧ ⟦ Y ⟧ → Frame X Y
    kmap  : ∀ {X Y} → Frame X Y → Frame (“M₀” X) (“M₀” Y)
    kunit : (X : “Ob”) → Frame X (“M₀” X)
    kmult : (X : “Ob”) → Frame (“M₀” (“M₀” X)) (“M₀” X)

  data Value : “Ob” → “Ob” → Type (o ⊔ h) where
    []  : ∀ {X} → Value X X
    _∷_ : ∀ {X Y Z} → Frame Y Z → Value X Y → Value X Z

  sem-frame : ∀ {X Y} → Frame X Y → Hom ⟦ X ⟧ ⟦ Y ⟧
  sem-frame (khom f) = f
  sem-frame (kmap k) = M₁ (sem-frame k)
  sem-frame (kunit X) = η ⟦ X ⟧
  sem-frame (kmult X) = μ ⟦ X ⟧

  sem-value : ∀ {X Y} → Value X Y → Hom ⟦ X ⟧ ⟦ Y ⟧
  sem-value [] = id
  sem-value (k ∷ v) = sem-frame k ∘ sem-value v

  instance
    Brackets-Frame : ∀ {X Y} → ⟦⟧-notation (Frame X Y)
    Brackets-Frame .⟦⟧-notation.lvl = h
    Brackets-Frame .⟦⟧-notation.Sem = _
    Brackets-Frame .⟦⟧-notation.⟦_⟧ = sem-frame

    Brackets-Value : ∀ {X Y} → ⟦⟧-notation (Value X Y)
    Brackets-Value .⟦⟧-notation.lvl = h
    Brackets-Value .⟦⟧-notation.Sem = _
    Brackets-Value .⟦⟧-notation.⟦_⟧ = sem-value

  --------------------------------------------------------------------------------
  -- Evaluation
  --
  -- The evaluation strategy here is a bit subtle. The naive option
  -- is to push the 'kunit' frames all the way to the bottom of the stack,
  -- but this makes enacting the 'μ ∘ η' equations inneficient, as that
  -- means we will also have to push the 'kmult' frames all the way to the bottom
  -- as well.
  --
  -- Instead, what we do is push the 'kmap' frames past all of the 'kunit' and 'kmult'
  -- frames, which ensures that all of the 'kunit' and 'kmult' frames remain on the top
  -- of the stack. This makes it easier to enact the equations in question, as
  -- we don't have to dig nearly as far.

  -- Concatenate 2 values together, performing no simplification.
  _++_ : ∀ {X Y Z} → Value Y Z → Value X Y → Value X Z
  [] ++ v2 = v2
  (k ∷ v1) ++ v2 = k ∷ (v1 ++ v2)

  -- Apply M₁ to a value.
  do-vmap : ∀ {X Y} → Value X Y → Value (“M₀” X) (“M₀” Y)
  do-vmap [] = []
  do-vmap (f ∷ v) = kmap f ∷ do-vmap v

  enact-laws : ∀ {W X Y Z} → Frame Y Z → Frame X Y → Value W X → Value W Z
  push-frm : ∀ {X Y Z} → Frame Y Z → Value X Y → Value X Z

  -- The meat of the solver! This is responsible for enacting the
  -- monad equations (hence the name).
  -- There are 2 important phases to this function: 'kunit' and 'kmult'
  -- floating, and the subsequent elimination of those frames.
  --
  -- When we push a 'kmap' frame, we check to see if the head of the stack
  -- is a 'kunit' or 'kmult'; if so, we float those outwards so that they
  -- always remain at the top of the stack.
  --
  -- Subsequently, when pushing a 'kmult' frame, we need to enact
  -- equations. As the relevant frames are /always/ on the top of the stack,
  -- we can simply apply the relevant equations, and potentially keep pushing
  -- frames down.
  enact-laws (khom f) k' v = khom f ∷ k' ∷ v
  enact-laws (kmap k) (khom g) v = kmap k ∷ khom g ∷ v
  enact-laws (kmap k) (kmap k') v = do-vmap (enact-laws k k' []) ++ v
  enact-laws (kmap k) (kunit _) v = kunit _ ∷ push-frm k v
  enact-laws (kmap k) (kmult _) v = kmult _ ∷ push-frm (kmap (kmap k)) v
  enact-laws (kunit _) k' v = kunit _ ∷ k' ∷ v
  enact-laws (kmult _) (khom g) v = kmult _ ∷ khom g ∷ v
  enact-laws (kmult _) (kmap (khom g)) v = kmult _ ∷ kmap (khom g) ∷ v
  enact-laws (kmult _) (kmap (kmap k')) v = kmult _ ∷ kmap (kmap k') ∷ v
  enact-laws (kmult _) (kmap (kunit _)) v = v
  enact-laws (kmult _) (kmap (kmult _)) v = kmult _ ∷ push-frm (kmult _) v
  enact-laws (kmult _) (kunit _) v = v
  enact-laws (kmult _) (kmult _) v = kmult _ ∷ kmult _ ∷ v

  -- Small shim, used to enact a law against a potentially empty stack.
  push-frm k [] = k ∷ []
  push-frm k (k' ∷ v) = enact-laws k k' v

  -- Concatenate 2 stacks together, performing simplification via 'enact-laws'.
  do-vcomp : ∀ {X Y Z} → Value Y Z → Value X Y → Value X Z
  do-vcomp [] v2 = v2
  do-vcomp (k ∷ v1) v2 = push-frm k (do-vcomp v1 v2)

  eval : ∀ {X Y} → “Hom” X Y → Value X Y
  eval (“M₁” e) = do-vmap (eval e)
  eval (“η” X) = kunit X ∷ []
  eval (“μ” X) = kmult X ∷ []
  eval (e1 “∘” e2) = do-vcomp (eval e1) (eval e2)
  eval “id” = []
  eval (f ↑) = khom f ∷ []

  --------------------------------------------------------------------------------
  -- Soundness

  vmap-sound : ∀ {X Y} → (v : Value X Y) → ⟦ do-vmap v ⟧ ≡ M₁ ⟦ v ⟧
  vmap-sound [] = sym M-id
  vmap-sound (k ∷ v) =
    M₁ ⟦ k ⟧ ∘ ⟦ do-vmap v ⟧ ≡⟨ refl⟩∘⟨ vmap-sound v ⟩
    M₁ ⟦ k ⟧ ∘ M₁ ⟦ v ⟧      ≡˘⟨ M-∘ ⟦ k ⟧ ⟦ v ⟧ ⟩
    M₁ (⟦ k ⟧ ∘ ⟦ v ⟧)       ∎

  vconcat-sound
    : ∀ {X Y Z}
    → (v1 : Value Y Z) (v2 : Value X Y)
    → ⟦ v1 ++ v2 ⟧ ≡ ⟦ v1 ⟧ ∘ ⟦ v2 ⟧
  vconcat-sound [] v2 = sym (idl ⟦ v2 ⟧)
  vconcat-sound (k ∷ v1) v2 = pushr (vconcat-sound v1 v2)

  enact-laws-sound
    : ∀ {W X Y Z}
    → (k1 : Frame Y Z) (k2 : Frame X Y) (v : Value W X)
    → ⟦ enact-laws k1 k2 v ⟧ ≡ ⟦ k1 ⟧ ∘ ⟦ k2 ⟧ ∘ ⟦ v ⟧
  push-frm-sound
    : ∀ {X Y Z}
    → (k : Frame Y Z) (v : Value X Y)
    → ⟦ push-frm k v ⟧ ≡ ⟦ k ⟧ ∘ ⟦ v ⟧

  enact-laws-sound (khom x) k2 v = refl
  enact-laws-sound (kmap k1) (khom g) v = refl
  enact-laws-sound (kmap k1) (kmap k2) v =
    ⟦ do-vmap (enact-laws k1 k2 []) ++ v ⟧    ≡⟨ vconcat-sound (do-vmap (enact-laws k1 k2 [])) v ⟩
    ⟦ do-vmap (enact-laws k1 k2 []) ⟧ ∘ ⟦ v ⟧ ≡⟨ vmap-sound (enact-laws k1 k2 []) ⟩∘⟨refl ⟩
    M₁ ⟦ enact-laws k1 k2 [] ⟧ ∘ ⟦ v ⟧        ≡⟨ M.pushl (enact-laws-sound k1 k2 []) ⟩
    M₁ ⟦ k1 ⟧ ∘ M₁ (⟦ k2 ⟧ ∘ id) ∘ ⟦ v ⟧      ≡⟨ refl⟩∘⟨ (M.⟨ idr ⟦ k2 ⟧ ⟩ ⟩∘⟨refl) ⟩
    M₁ ⟦ k1 ⟧ ∘ M₁ ⟦ k2 ⟧ ∘ ⟦ v ⟧             ∎
  enact-laws-sound (kmap {Y = Y} k1) (kunit X) v =
    η ⟦ Y ⟧ ∘ ⟦ push-frm k1 v ⟧   ≡⟨ refl⟩∘⟨ push-frm-sound k1 v ⟩
    η ⟦ Y ⟧ ∘ ⟦ k1 ⟧ ∘ ⟦ v ⟧      ≡⟨ extendl (unit.is-natural ⟦ X ⟧ ⟦ Y ⟧ ⟦ k1 ⟧) ⟩
    M.F₁ ⟦ k1 ⟧ ∘ η ⟦ X ⟧ ∘ ⟦ v ⟧ ∎
  enact-laws-sound (kmap {Y = Y} k1) (kmult X) v =
    μ ⟦ Y ⟧ ∘ ⟦ push-frm (kmap (kmap k1)) v ⟧ ≡⟨ refl⟩∘⟨ push-frm-sound (kmap (kmap k1)) v ⟩
    μ ⟦ Y ⟧ ∘ M₁ (M₁ ⟦ k1 ⟧) ∘ ⟦ v ⟧          ≡⟨ extendl (mult.is-natural ⟦ X ⟧ ⟦ Y ⟧ ⟦ k1 ⟧) ⟩
    M.F₁ ⟦ k1 ⟧ ∘ μ ⟦ X ⟧ ∘ ⟦ v ⟧             ∎
  enact-laws-sound (kunit X) k2 v = refl
  enact-laws-sound (kmult X) (khom g) v = refl
  enact-laws-sound (kmult X) (kmap (khom g)) v = refl
  enact-laws-sound (kmult X) (kmap (kmap k2)) v = refl
  enact-laws-sound (kmult X) (kmap (kunit .X)) v = insertl μ-unitr
  enact-laws-sound (kmult X) (kmap (kmult .X)) v =
    μ ⟦ X ⟧ ∘ ⟦ push-frm (kmult (“M₀” X)) v ⟧ ≡⟨ refl⟩∘⟨ push-frm-sound (kmult (“M₀” X)) v ⟩
    μ ⟦ X ⟧ ∘ μ (M₀ ⟦ X ⟧) ∘ ⟦ v ⟧       ≡⟨ extendl (sym μ-assoc) ⟩
    μ ⟦ X ⟧ ∘ M₁ (μ ⟦ X ⟧) ∘ ⟦ v ⟧       ∎
  enact-laws-sound (kmult X) (kunit _) v = insertl μ-unitl
  enact-laws-sound (kmult X) (kmult _) v = refl

  push-frm-sound k [] = refl
  push-frm-sound k (k' ∷ v) = enact-laws-sound k k' v

  vcomp-sound
    : ∀ {X Y Z}
    → (v1 : Value Y Z) (v2 : Value X Y)
    → ⟦ do-vcomp v1 v2 ⟧ ≡ ⟦ v1 ⟧ ∘ ⟦ v2 ⟧
  vcomp-sound [] v2 = sym (idl ⟦ v2 ⟧)
  vcomp-sound (k ∷ v1) v2 =
    ⟦ push-frm k (do-vcomp v1 v2) ⟧ ≡⟨ push-frm-sound k (do-vcomp v1 v2) ⟩
    ⟦ k ⟧ ∘ ⟦ do-vcomp v1 v2 ⟧      ≡⟨ pushr (vcomp-sound v1 v2) ⟩
    (⟦ k ⟧ ∘ ⟦ v1 ⟧) ∘ ⟦ v2 ⟧       ∎

  eval-sound : ∀ {X Y} → (e : “Hom” X Y) → ⟦ eval e ⟧ ≡ ⟦ e ⟧
  eval-sound (“M₁” e) =
    ⟦ do-vmap (eval e) ⟧ ≡⟨ vmap-sound (eval e) ⟩
    M₁ ⟦ eval e ⟧        ≡⟨ ap M₁ (eval-sound e) ⟩
    M₁ ⟦ e ⟧             ∎
  eval-sound (“η” X) = idr (η ⟦ X ⟧)
  eval-sound (“μ” X) = idr (μ ⟦ X ⟧)
  eval-sound (e1 “∘” e2) =
    ⟦ do-vcomp (eval e1) (eval e2) ⟧ ≡⟨ vcomp-sound (eval e1) (eval e2) ⟩
    ⟦ eval e1 ⟧ ∘ ⟦ eval e2 ⟧        ≡⟨ ap₂ _∘_ (eval-sound e1) (eval-sound e2) ⟩
    ⟦ e1 ⟧ ∘ ⟦ e2 ⟧                  ∎
  eval-sound “id” = refl
  eval-sound (f ↑) = idr f

module _ {o h} {C : Precategory o h} {M : Functor C C} {monad : Monad-on M} where
  private
    open Cat.Reasoning C
    open Monad-on monad
    module M = Cat.Functor.Reasoning M
    open NbE monad

  record Monad-ob (X : Ob) : Typeω where
    field
      “ob” : “Ob”
      ob-repr : ⟦ “ob” ⟧ ≡ᵢ X

  “ob” : (X : Ob) → ⦃ “X” : Monad-ob X ⦄ → “Ob”
  “ob” X ⦃ “X” ⦄ = Monad-ob.“ob” “X”

  ob-repr : (X : Ob) → ⦃ “X” : Monad-ob X ⦄ → ⟦ “ob” X ⟧ ≡ᵢ X
  ob-repr X ⦃ “X” ⦄ = Monad-ob.ob-repr “X”

  record Monad-hom
    {X Y : Ob}
    ⦃ “X” : Monad-ob X ⦄ ⦃ “Y” : Monad-ob Y ⦄
    (f : Hom X Y) : Typeω where
    field
      “hom” : “Hom” (“ob” X) (“ob” Y)

  “hom”
    : ∀ {X Y : Ob} → (f : Hom X Y)
    → ⦃ “X” : Monad-ob X ⦄ ⦃ “Y” : Monad-ob Y ⦄
    → ⦃ “f” : Monad-hom f ⦄
    → “Hom” (“ob” X) (“ob” Y)
  “hom” f ⦃ “f” = “f” ⦄ = Monad-hom.“hom” “f”

  instance
    Monad-ob-Default
      : ∀ {X} → Monad-ob X
    Monad-ob-Default {X = X} .Monad-ob.“ob” = NbE.“ X ”
    Monad-ob-Default .Monad-ob.ob-repr = reflᵢ
    {-# INCOHERENT Monad-ob-Default #-}

    Monad-ob-M₀ : ∀ {X} → ⦃ “X” : Monad-ob  X ⦄ → Monad-ob (M₀ X)
    Monad-ob-M₀ {X = X} .Monad-ob.“ob” = “M₀” (“ob” X)
    Monad-ob-M₀ {X = X} .Monad-ob.ob-repr = apᵢ M₀ (ob-repr X)

    Monad-hom-Default
      : ∀ {X Y} {f : Hom X Y}
      → ⦃ “X” : Monad-ob X ⦄ ⦃ “Y” : Monad-ob Y ⦄
      → Monad-hom f
    Monad-hom-Default {X = X} {Y = Y} {f = f} .Monad-hom.“hom” =
      substᵢ (λ X → Hom X ⟦ “ob” Y ⟧) (symᵢ (ob-repr X)) (substᵢ (λ Y → Hom X Y) (symᵢ (ob-repr Y)) f) ↑
    {-# INCOHERENT Monad-hom-Default #-}

    Monad-hom-M₁
      : ∀ {X Y} {f : Hom X Y}
      → ⦃ “X” : Monad-ob X ⦄ ⦃ “Y” : Monad-ob Y ⦄
      → ⦃ “f” : Monad-hom f ⦄
      → Monad-hom (M₁ f)
    Monad-hom-M₁ {f = f} .Monad-hom.“hom” = “M₁” (“hom” f)

    Monad-hom-η
      : ∀ {X}
      → ⦃ “X” : Monad-ob X ⦄
      → Monad-hom (η X)
    Monad-hom-η {X = X} .Monad-hom.“hom” = “η” (“ob” X)

    Monad-hom-μ
      : ∀ {X}
      → ⦃ “X” : Monad-ob X ⦄
      → Monad-hom (μ X)
    Monad-hom-μ {X = X} .Monad-hom.“hom” = “μ” (“ob” X)

    Monad-hom-∘
      : ∀ {X Y Z} {f : Hom Y Z} {g : Hom X Y}
      → ⦃ “X” : Monad-ob X ⦄ ⦃ “Y” : Monad-ob Y ⦄ ⦃ “Z” : Monad-ob Z ⦄
      → ⦃ “f” : Monad-hom f ⦄ ⦃ “g” : Monad-hom g ⦄
      → Monad-hom (f ∘ g)
    Monad-hom-∘ {f = f} {g = g} .Monad-hom.“hom” = “hom” f “∘” “hom” g

    Monad-hom-id
      : ∀ {X}
      → ⦃ “X” : Monad-ob X ⦄
      → Monad-hom (id {X})
    Monad-hom-id {X = X} .Monad-hom.“hom” = “id” {X = “ob” X}


abstract
  solve-monad
    : ∀ {o h} {C : Precategory o h} {M : Functor C C} (monad : Monad-on M)
    → (let open Precategory C) (let open NbE monad)
    → ∀ {X Y}
    → (f g : Hom X Y)
    → ⦃ “X” : Monad-ob X ⦄ ⦃ “Y” : Monad-ob Y ⦄
    → ⦃ “f” : Monad-hom f ⦄ ⦃ “g” : Monad-hom g ⦄
    → ⟦ eval (“hom” f) ⟧ ≡ ⟦ eval (“hom” g) ⟧ → ⟦ “hom” f ⟧ ≡ ⟦ “hom” g ⟧
  solve-monad monad f g p = sym (NbE.eval-sound monad (“hom” f)) ·· p ·· NbE.eval-sound monad (“hom” g)

macro
  monad! : ∀ {o h} {C : Precategory o h} {F : Functor C C} → Monad-on F → Term → TC ⊤
  monad! monad hole =
    withNormalisation false $ do
    goal ← infer-type hole >>= reduce
    just (lhs , rhs) ← get-boundary goal
      where nothing → typeError $ strErr "Can't determine boundary: " ∷
                                  termErr goal ∷ []
    “monad” ← quoteTC monad
    unify hole (def (quote solve-monad) (“monad” v∷ lhs v∷ rhs v∷ “refl” v∷ []))

private module Test {o h} {𝒞 : Precategory o h} {M : Functor 𝒞 𝒞} (monad : Monad-on M) where
  open Precategory 𝒞
  open Monad-on monad

  variable
    A B C : Ob

  test : ∀ {f : Hom B C} {g : Hom A B}
         → μ C ∘ M₁ (M₁ (f ∘ g)) ∘ η (M₀ A) ≡ M₁ f ∘ M₁ (id ∘ g)
  test = monad! monad

  test-assoc : ∀ X → μ X ∘ M₁ (μ X) ≡ μ X ∘ μ (M₀ X)
  test-assoc X = monad! monad

  test-nested : ∀ X → M₁ (μ X ∘ η (M₀ X)) ≡ id
  test-nested _ = monad! monad

  test-separate : ∀ X → M₁ (μ X) ∘ M₁ (η (M₀ X)) ≡ id
  test-separate _ = monad! monad
