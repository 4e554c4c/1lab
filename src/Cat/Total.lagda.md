<!--
```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Colimit.Terminal
open import Cat.Diagram.Coproduct.Copower
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Diagram.Duals
open import Cat.Diagram.Initial
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Terminal
open import Cat.Functor.Adjoint
open import Cat.Functor.Adjoint.AFT
open import Cat.Functor.Adjoint.Colimit
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Adjoint.Kan
open import Cat.Functor.Adjoint.Reflective
open import Cat.Functor.Base
open import Cat.Functor.Compose
open import Cat.Functor.Constant
open import Cat.Functor.Equivalence
open import Cat.Functor.Final
open import Cat.Functor.Hom.Coyoneda
open import Cat.Functor.Hom.Duality
open import Cat.Functor.Hom.Representable
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Kan.Adjoint
open import Cat.Functor.Kan.Base
open import Cat.Functor.Kan.Nerve
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Naturality
open import Cat.Instances.Comma
open import Cat.Instances.Discrete
open import Cat.Instances.Elements
open import Cat.Instances.Elements.Properties
open import Cat.Instances.Functor
open import Cat.Instances.Sets.Complete
open import Cat.Instances.Shape.Terminal
open import Cat.Prelude hiding (J)
open import Cat.Diagram.Separator

import Cat.Diagram.Colimit.Coproduct
import Cat.Morphism
import Cat.Functor.Reasoning

```
-->

```agda
module Cat.Total {o ℓ} (C : Precategory o ℓ) where
open import Cat.Functor.Hom C
open import Cat.Instances.Presheaf.Colimits
```
<!--
```agda
private
  open module C = Precategory C
  variable
    o' ℓ' : Level
    E : Precategory o' ℓ'
    J : Precategory o' ℓ'
```
-->

# Total precategories {defines="total-precategory"}

A precategory is **total** if its yoneda embedding has a left adjoint.

```agda
record is-total : Type (o ⊔ lsuc ℓ) where
  field
    {れ} : Functor Cat[ C ^op , Sets ℓ ] C
    has-よ-adj : れ ⊣ よ
  open module れ = Cat.Functor.Reasoning れ using () renaming (F₀ to れ₀; F₁ to れ₁) public

```

## Free objects relative to よ

Before we investigate the properties of a total category, it's worth
considering the action of such a functor on objects, if it exists. Given
some presheaf $$F\in\psh(\cC)$$, an object could be $れ(F)$ if it is [[free|universal morphism]]
with respect to $\yo$.

```agda
module _ (F : Functor (C ^op) (Sets ℓ)) (c : Free-object よ F) where
```
<!--
```agda
  open Free-object c
```
-->

Since $F$ is a presheaf, it can be written as a colimit of representable
functors by the [[coyoneda lemma]].

As left adjoints preserve colimits, our object `c` must also be a colimit
of objects in $\cC$. This object can be called the corepresentation of $F$.

```agda
  private
    F-is-colimit : is-colimit (よ F∘ πₚ C F) F _
    F-is-colimit = coyoneda _ F
  free-is-colimit : make-is-colimit (πₚ C F) free
  free-is-colimit = free-object→make-is-colimit よ よ-is-fully-faithful (to-colimit F-is-colimit) c
```

<!--
```agda
module Total (C-total : is-total) where
  open module C-total = is-total C-total public
  open Cat.Morphism C public

  れ∘よ≅ⁿid : れ F∘ よ ≅ⁿ Id
  れ∘よ≅ⁿid = is-reflective→counit-iso has-よ-adj よ-is-fully-faithful

  private
    れ∘よ∘F≅ⁿF : ∀ {F : Functor J C} → れ F∘ よ F∘ F ≅ⁿ F
    れ∘よ∘F≅ⁿF = ni-assoc ∙ni (れ∘よ≅ⁿid ◂ni _) ∙ni path→iso F∘-idl

  module _ (F : ⌞ PSh ℓ C ⌟) where
    private
```
-->


## れ on values

```agda
      F-is-colimit : is-colimit (よ F∘ πₚ C F) F _
      F-is-colimit = coyoneda _ F
    -- this would be better to prove for an arbitrary free object w.r.t. よ
    -- where we don't assume that れ exists...
    -- but it's hard for me to show that colimits of an arbitrary free object
    -- w.r.t. a ff functor are computed in C
    れ₀-is-colimit : is-colimit (πₚ C F) (れ₀ F) _
    れ₀-is-colimit = natural-isos→is-lan idni れ∘よ∘F≅ⁿF (!const-isoⁿ id-iso) refl(left-adjoint-is-cocontinuous has-よ-adj F-is-colimit)
```

## Cocompleteness

All total categories are [[cocomplete]].

```agda
  cocomplete : is-cocomplete ℓ ℓ C
  cocomplete F = natural-iso→colimit れ∘よ∘F≅ⁿF $ left-adjoint-colimit has-よ-adj $ Psh-cocomplete ℓ C (よ F∘ F)
```

## Terminal object?

```agda
  open Terminal (Sets-terminal {ℓ = ℓ}) renaming (top to s★)
  -- look at this funny guy
  c : ⌞ PSh ℓ C ⌟
  c = Const $ s★

  -- he has a corepresentation
  ★ : C.Ob
  ★ = れ.₀ c

  -- what do we know about this thing? it's a colimit
  private
    ★-is-colimit-id : is-colimit (Id {C = C}) ★ _
    ★-is-colimit-id = extend-is-colimit _ (right-adjoint-is-final (elements-terminal-is-equivalence.F⁻¹⊣F {s = ℓ})) _ col'
      where
      open is-equivalence
      col : is-colimit (πₚ C $ Const $ s★) ★ _
      col = れ₀-is-colimit _
      col' : is-colimit (Id F∘ πₚ C (Const s★)) ★ _
      col' = natural-iso-ext→is-lan (left-adjoint-is-cocontinuous (Id-is-equivalence .F⊣F⁻¹) col) (!const-isoⁿ id-iso)

  -- and thus is terminal
  total-terminal : Terminal C
  total-terminal = Id-colimit→Terminal $ to-colimit ★-is-colimit-id

  module total-terminal = Terminal total-terminal

  _ : total-terminal.top ≡ ★
  _ = refl

```



## Copowers

As `C` is cocomplete, it has all set-indexed coproducts
```agda
  open Cat.Diagram.Colimit.Coproduct C
  has-set-indexed-coproducts : (S : Set ℓ) → has-coproducts-indexed-by C ∣ S ∣
  has-set-indexed-coproducts S F = Colimit→IC F (cocomplete $ Disc-adjunct F)
```

and is thus copowered
```agda
  open Copowers has-set-indexed-coproducts public
  open Consts total-terminal has-set-indexed-coproducts public
```


# Separators

```agda
{-
  ★-is-separator : is-separator C ★
  ★-is-separator = epi→separator C has-set-indexed-coproducts λ { {x} f g p → {! p !} } where
    p : ∀ {x y} → {f g : x → y}  →
-}
  ★-is-dense-separator : is-dense-separator C ★
  ★-is-dense-separator = coyoneda→dense-separator C λ x →
    is-colimit→is-indexed-coprduct (λ { e → ★ }) {! !}

```


## The adjoint functor property

Total precategories satisfy a particularly nice [[adjoint functor theorem]]. In
particular, every [[continuous functor]] $F$ has a [[left adjoint]].


```agda
  cocontinuous→right-adjoint : ∀ {D : Precategory ℓ ℓ}
    (F : Functor C D) → is-cocontinuous (o ⊔ ℓ) ℓ F → Σ[ G ∈ Functor D C ] F ⊣ G
  cocontinuous→right-adjoint {D = D} F F-is-cocont = Functor.op (aft .fst) , opposite-adjunction (aft .snd) where
    module F = Functor F
    aft = formal-aft F.op (is-cocontinuous→co-is-continuous F-is-cocont) λ {x} Q → {! Colimit→Co-limit $ cocomplete  ?!}
{-
G , F⊣G where
    module F = Functor F
    module D = Precategory D
    open import Cat.Functor.Hom D using () renaming (Hom-into to Hom-intoᴰ; よ to よᴰ )

```

Given $F$, there is an obvious choice for $G$ given by the nerve of $F$ composed with $れ$.
```agda
    G : Functor D C
    G = れ F∘ Nerve F
    module G = Functor G
    _ : Functor D (PSh _ C)
    _ = precompose F.op F∘ よᴰ

    F⊣G : F ⊣ G
    F⊣G = is-absolute-lan→adjoint G-is-lan-H where
```

--Realisation-is-lan : is-lan (よ C) F Realisation approx

```agda
      -- first, we note that the G is a lan. Since $れ$ is a left adjoint and preserves that the nerve is a lan
      G-is-lan : is-lan F (れ F∘ よ) G _
      G-is-lan = left-adjoint→preserves-lan has-よ-adj (Nerve-is-lan F)

      -- but (れ F∘ よ) is the identity
      G-is-lan-Id : is-lan F Id G _
      G-is-lan-Id = natural-iso-of→is-lan G-is-lan れ∘よ≅ⁿid


      -- so here we try something a bit tricky

      -- we need to get a lan precomposed with H
      G-is-lan-H : {E : Precategory o' ℓ'} → (H : Functor C E) → is-lan F (H F∘ Id) (H F∘ G) _
      G-is-lan-H {E = E} H = {!  !} where
        --foo : is-lan (precompose F)
        _ : is-lan F ((H F∘ れ) F∘ よ) ((H F∘ れ) F∘ Nerve F) _
        _ = left-adjoint→preserves-lan {!has-よ-adj !} (Nerve-is-lan F)

{-
    open _⊣_
    F⊣G : F ⊣ G
    F⊣G .unit = ni-assoc .Isoⁿ.to ∘nt (れ ▸ coapprox F) ∘nt れ∘よ≅ⁿid .Isoⁿ.from
    --F⊣G .counit = {! !}
    -- here i need F (れ (よ₀ D d F∘ Fᵒᵖ)) -> d
    -- F is cocontinuous so it maps colimits to colimits
    -- and we know the inside is a colimit. in particular
    -- れ (よ₀ d F∘ Fᵒᵖ) = colimit πₚ C (よ₀ d F∘ Fᵒᵖ)

    F⊣G .counit ._=>_.η d = {! !}
    F⊣G .counit ._=>_.is-natural x y f = {! !}
    F⊣G .zig = {! !}
    F⊣G .zag = {! !}
-}
-}


    -- ok lets try again
    --F⊣G' : F ⊣ G
    --F⊣G' = hom-iso→adjoints
```
