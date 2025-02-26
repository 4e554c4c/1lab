<!--
```agda
open import Cat.Prelude hiding (∣_∣)
```
-->

```agda
module Cat.Double.Virtual (ℓo ℓt ℓl ℓ□ : Level)  where
```

# Virtual double categories


<!--
```agda
import Cat.Reasoning as R
open import Cat.Instances.Shape.Cospan using (·←·→·)
open import Cat.Functor.Base using (Cat[_,_])
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Universe
open import 1Lab.Reflection

level-of-vdbl : Level
level-of-vdbl = (lsuc (ℓo ⊔ ℓt ⊔ ℓl ⊔ ℓ□))
```
-->

Virtual double categories are similar to double categories, but lack a composition
operation for their horizontal arrows. We accommodate this lack of structure by
allowing 2-cells between arrows of arbitrary *arity*. In particular, we need to be
able to represent a "multi-arrow" between $A$ and $B$ which may contain several
individual arrows. In some sense, we are asking for a graph $G$ and the arrows of the
[[free-category]] over that graph.


```agda
module multi {o a : Level} (Ob : Type o) (Arr : Ob → Ob → Type a) where
  data MultiArr : Ob → Ob → Type (o ⊔ a) where
    [] : {X : Ob} → MultiArr X X
    cons : ∀ {X : Ob} {M : Ob} {Y : Ob} → Arr X M → MultiArr M Y → MultiArr X Y
  syntax cons {M = M} h m = h :⟨ M ⟩: m

  infixr 40 _⊛_
  _⊛_ : ∀ {a b c} → MultiArr a b → MultiArr b c → MultiArr a c
  _⊛_ [] m = m
  _⊛_ (cons f ms) m = cons f (ms ⊛ m)

  ⊛-cancelr : ∀ {a b} (m : MultiArr a b) → (m ⊛ []) ≡ m
  ⊛-cancelr [] = refl
  ⊛-cancelr (cons f ms) = ap (cons f) (⊛-cancelr ms)

  ⊛-assoc : ∀ {a b c d} (f : MultiArr a b) (g : MultiArr b c) (h : MultiArr c d)
                → f ⊛ g ⊛ h ≡ (f ⊛ g) ⊛ h
  ⊛-assoc [] g h = refl
  ⊛-assoc (cons f fs) g h = ap (cons f) (⊛-assoc fs g h)

  {-# REWRITE ⊛-cancelr ⊛-assoc #-}

  single : ∀ {X Y} → Arr X Y → MultiArr X Y
  single a = cons a []


record VirtualDoubleCategoryData : Type level-of-vdbl where
  no-eta-equality
  field
    TightCat  : Precategory ℓo ℓt
  open module TightCat = R TightCat renaming (Hom to Tight; Hom-set to Tight-set; idr to tidr; idl to tidl; assoc to tassoc) public
  field
    Loose : Ob → Ob → Type ℓl
  open multi Ob Loose public

  _↓_ = Tight
  _⇸_ = Loose
  _⇸⋯⇸_ = MultiArr

  field
    -- is this necessary?
    Loose-set : (x y : Ob) → is-set (x ⇸ y)
    Cell : ∀ {X X' Y Y'}  (m : X ⇸⋯⇸ Y) (f : X ↓ X') (g : Y ↓ Y') (q : X' ⇸ Y')   → Type ℓ□

  ┌_┐_□_└_┘ = Cell

  field
    id□ : ∀ {X Y} (p : X ⇸ Y)
          → ┌ single p ┐
             id   □  id
            └     p    ┘

  data Multi□ : {A B C D : Ob} (top : A ⇸⋯⇸ B) (f : A ↓ C) (g : B ↓ D) (bot : C ⇸⋯⇸ D)  → Type level-of-vdbl where
    □[] : {A C : Ob} → {f : A ↓ C} → Multi□ [] f f []
    □cons : {A B C D E F : Ob}
             → {f : A ↓ C} {top : A ⇸⋯⇸ B} {p : C ⇸ D} {g : B ↓ D} {top' : B ⇸⋯⇸ E} {bot : D ⇸⋯⇸ F} {h : E ↓ F}
             → Cell top f g p → Multi□ top' g h bot → Multi□ (top ⊛ top') f h (cons p bot)

  ┌_┐_□⋯□_└_┘ = Multi□

  single□ : ∀ {X X' Y Y'} {f : X ↓ X'} {m : X ⇸⋯⇸ Y} {q : X' ⇸ Y'} {g : Y ↓ Y'}
          → ┌   m   ┐
              f □ g
            └   q   ┘
          → ┌     m    ┐
             f   □⋯□  g
            └ single q ┘
  single□ a = □cons a □[]

  idMCell : ∀ {X Y} → (m : X ⇸⋯⇸ Y)
          → ┌   m   ┐
            id □⋯□ id
            └   m   ┘
  idMCell [] = □[]
  idMCell (cons p as) = □cons (id□ p) (idMCell as)

  m□concat : ∀ {X X' Y Y' Z Z'} {f : X ↓ X'}  {g : Y ↓ Y'} {h : Z ↓ Z'}
          → {t₁ : X ⇸⋯⇸ Y} {t₂ : Y ⇸⋯⇸ Z} {b₁ : X' ⇸⋯⇸ Y'} {b₂ : Y' ⇸⋯⇸ Z'}
          → ┌  t₁  ┐
             f □⋯□ g
            └  b₁  ┘
          → ┌  t₂  ┐
             g □⋯□ h
            └  b₂  ┘
          → ┌  t₁ ⊛ t₂  ┐
               f □⋯□ h
            └  b₁ ⊛ b₂  ┘
  m□concat □[] βs = βs
  m□concat (□cons {B = χ} {D = χ'} α αs) βs = □cons α (m□concat αs βs)
```

Given a multicell $\mathfrak{a}$ whose base is a composite multiarrow $M₁\circ M₂$ we
may successfully split $\mathfrak{a}$ into two multicells: $\mathfrak{a}_1$ with base
$M₁$ and $\mathfrak{a}_2$ with base $M₂$---as each cell has a unique base arrow.

However, we do not know what the top of $\mathfrak{a}_1$ and $\mathfrak{a}_2$ will
be; or what arrow they will share. Therefore, the output of our splitting algorithm
will contain two cells whose whose bottom is known, along with a guarantee that when
recombined the top multiarrow will be preserved.

We bundle all of this information into a helper structure.


```agda
  record Msplit {X X' Y Y' χ' }
                {f : X ↓ X'} {g : Y ↓ Y'} {t : X ⇸⋯⇸ Y}
                (b₁ : X' ⇸⋯⇸ χ') (b₂ : χ' ⇸⋯⇸ Y')
                (𝔞 : ┌    t    ┐
                       f □⋯□ g
                     └ b₁ ⊛ b₂ ┘) : Type level-of-vdbl where
    field
      {χ}  : Ob
      {fᵡ} : χ ↓ χ'
      {t₁} : X ⇸⋯⇸ χ
      {t₂} : χ ⇸⋯⇸ Y
      p   : t₁ ⊛ t₂ ≡ t
      𝔞₁   : ┌   t₁  ┐
              f □⋯□ fᵡ
             └   b₁  ┘

      𝔞₂   : ┌   t₂  ┐
              fᵡ □⋯□ g
             └   b₂  ┘

  -- we can split on the bottom of a multicell, but recovering the top split definitionally is impossible.
  -- instead we provide a proof that the top splits well
  msplit : ∀ {X X' Y Y' χ'} {f : X ↓ X'}  {h : Y ↓ Y'}
          → {t : X ⇸⋯⇸ Y}
          → {b₁ : X' ⇸⋯⇸ χ'} {b₂ : χ' ⇸⋯⇸ Y'}
          → (𝔞 : ┌    t    ┐
                   f □⋯□ h
                 └ b₁ ⊛ b₂ ┘)
          → Msplit b₁ b₂ 𝔞
  msplit {X = X} {f = f} {t = t} {b₁ = []} 𝔞 = record { p = refl ; 𝔞₁ = □[] ; 𝔞₂ = 𝔞 }
  msplit {b₁ = cons b bs} {b₂ = b₂} (□cons {top = t₁} α 𝔞) =
    record { p = ap (t₁ ⊛_) split.p
           ; 𝔞₁ = □cons α split.𝔞₁
           ; 𝔞₂ = split.𝔞₂
           } where
    split = msplit 𝔞
    module split = Msplit split


record VirtualDoubleCategoryStructure (d : VirtualDoubleCategoryData) : Type level-of-vdbl where
  open VirtualDoubleCategoryData d public

  field
    vcomp : ∀ {X X' X'' f Y Y' Y'' g q} {f' : X' ↓ X''} {g' : Y' ↓ Y''} {top : X ⇸⋯⇸ Y} {mid : X' ⇸⋯⇸ Y'}
          → ┌  top  ┐
             f □⋯□ g
            └  mid  ┘
          → ┌  mid  ┐
             f' □  g'
            └   q   ┘
          → ┌      top       ┐
             f' ∘ f □  g' ∘ g
            └       q        ┘

  vccomp : ∀ {X X' X'' Y Y' Y'' f g} {f' : X' ↓ X''} {g' : Y' ↓ Y''} {top : X ⇸⋯⇸ Y} {mid : X' ⇸⋯⇸ Y'} {bot : X'' ⇸⋯⇸ Y''}
        → ┌   top   ┐
           f  □⋯□  g
          └   mid   ┘
        → ┌   mid   ┐
           f' □⋯□  g'
          └   bot   ┘
        → ┌       top       ┐
           f' ∘ f □⋯□ g' ∘ g
          └       bot       ┘
  -- this is weird, because the constraints on everything means that m must be []
  -- but asking agda to figure that out is a bit too much
  vccomp {top = []} {mid = m} {bot = []} □[] □[] = □[]
  {-# CATCHALL #-}
  -- now we know that 𝔞 is a split, so we can split it and compose with `b`
  vccomp {f = f} {g} {f'} {g'} {bot = bot} 𝔞 (□cons b 𝔟) =
    transport (λ i → ┌       p i       ┐
                      f' ∘ f □⋯□ g' ∘ g
                     └       bot       ┘) $
              □cons (vcomp 𝔞₁ b) (vccomp 𝔞₂ 𝔟) where
    split = msplit 𝔞
    open Msplit split

record VirtualDoubleCategoryLaws {d} (s : VirtualDoubleCategoryStructure d) : Type level-of-vdbl where
  open VirtualDoubleCategoryStructure s public

  field
    idt : ∀ {X X' Y Y' q} (f : X ↓ X') (g : Y ↓ Y') (m : X ⇸⋯⇸ Y)
        → (α : ┌  m  ┐
                f □ g
               └  q  ┘)
        → PathP (λ i → Cell m (tidr f i) (tidr g i) q) (vcomp (idMCell m) α) α
    idb : ∀ {X X' Y Y' q} (f : X ↓ X') (g : Y ↓ Y') (m : X ⇸⋯⇸ Y)
        → (α : ┌  m  ┐
                f □ g
               └  q  ┘)
        → PathP (λ i → Cell m (tidl f i) (tidl g i) q) (vcomp (single□ α) (id□ q)) α

    assoc : ∀ {X X' X'' X''' Y Y' Y'' Y''' f f' f'' g g' g''}
          → (top : X ⇸⋯⇸ Y) (mid₁ : X' ⇸⋯⇸ Y') (mid₂ : X'' ⇸⋯⇸ Y'') (q : X''' ⇸ Y''')
          → (α₁ : ┌   top   ┐
                   f  □⋯□  g
                  └   mid₁  ┘)
          → (α₂ : ┌   mid₁  ┐
                   f' □⋯□  g'
                  └   mid₂  ┘)
          → (α₃ : ┌   mid₂  ┐
                   f'' □   g''
                  └    q    ┘)
          → PathP (λ i → Cell top (tassoc f'' f' f i) (tassoc g'' g' g i) q)
                  (vcomp (vccomp α₁ α₂) α₃)
                  (vcomp α₁ (vcomp α₂ α₃))
  level = level-of-vdbl

record VirtualDoubleCategory : Type level-of-vdbl where
  no-eta-equality
  field
    Data : VirtualDoubleCategoryData
    Struct : VirtualDoubleCategoryStructure Data
    Laws : VirtualDoubleCategoryLaws Struct
  open VirtualDoubleCategoryLaws Laws public
```
