---
description: |
  The category of graphs.
---
<!--
```agda
open import 1Lab.Path.Cartesian
open import 1Lab.Reflection

open import Cat.Functor.Equivalence.Path
open import Cat.Instances.StrictCat
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Univalent
open import Cat.Prelude
open import Cat.Strict
open import Cat.Instances.Shape.Parallel --using (·←·→·)

import Cat.Morphism
import Cat.Reasoning
```
-->
```agda
module Cat.Instances.Graphs where
```

<!--
```agda
private variable
  o o' ℓ ℓ' : Level
```
-->

# The category of graphs

:::{.definition #graph}
A **graph** (really, an $(o, \ell)$-graph^[and, even more pedantically,
a directed multi-$(o, ℓ)$-graph]) is given by a set $V : \Sets_o$ of
**vertices** and, for each pair of elements $x, y : V$, a set of
**edges** $E(x, y) : \Sets_\ell$ from $x$ to $y$. That's it: a set $V$
and a family of sets over $V \times V$.
:::


```agda
record Graph (o ℓ : Level) : Type (lsuc o ⊔ lsuc ℓ) where
  no-eta-equality
  field
    Vertex : Type o
    Edge : Vertex → Vertex → Type ℓ
    Vertex-is-set : is-set Vertex
    Edge-is-set : ∀ {x y} → is-set (Edge x y)
```

<!--
```agda
open Graph
open hlevel-projection

instance
  Underlying-Graph : Underlying (Graph o ℓ)
  Underlying-Graph = record { ⌞_⌟ = Graph.Vertex }

  hlevel-proj-vertex : hlevel-projection (quote Graph.Vertex)
  hlevel-proj-vertex .has-level = quote Graph.Vertex-is-set
  hlevel-proj-vertex .get-level _ = pure (quoteTerm (suc (suc zero)))
  hlevel-proj-vertex .get-argument (_ ∷ _ ∷ c v∷ _) = pure c
  {-# CATCHALL #-}
  hlevel-proj-vertex .get-argument _ = typeError []

  hlevel-proj-edge : hlevel-projection (quote Graph.Edge)
  hlevel-proj-edge .has-level = quote Graph.Edge-is-set
  hlevel-proj-edge .get-level _ = pure (quoteTerm (suc (suc zero)))
  hlevel-proj-edge .get-argument (_ ∷ _ ∷ c v∷ _) = pure c
  {-# CATCHALL #-}
  hlevel-proj-edge .get-argument _ = typeError []

Graph-path : ∀ {o ℓ} → {G H : Graph o ℓ}
  → (pᵥ : G .Vertex ≡ H .Vertex)
  → PathP (λ i → (u v : pᵥ i) → Type ℓ) (G .Edge) (H .Edge)
  → G ≡ H
Graph-path p _ i .Vertex = p i
Graph-path pᵥ pₑ i .Edge u v = pₑ i u v
Graph-path {G = G} {H = H} pᵥ pₑ i .Vertex-is-set = is-prop→pathp (λ i → is-hlevel-is-prop {A = pᵥ i} 2) (G .Vertex-is-set) (H .Vertex-is-set) i
Graph-path {G = G} {H = H} pᵥ pₑ i .Edge-is-set {u} {v} = is-prop→pathp {B = λ i → {u v : pᵥ i} → is-set (pₑ i u v)} (λ _ → hlevel 1) (G .Edge-is-set) (H .Edge-is-set) i
```
-->

:::{.definition #graph-homomorphism}
A **graph homomorphism** $G \to H$ consists of a mapping of vertices
$f_v : G \to H$, along with a mapping of edges $f_e : G(x, y) \to H(f_v(x), f_v(y))$.
:::


```agda
record Graph-hom (G : Graph o ℓ) (H : Graph o' ℓ') : Type (o ⊔ o' ⊔ ℓ ⊔ ℓ') where
  no-eta-equality
  field
    vertex : ⌞ G ⌟ → ⌞ H ⌟
    edge : ∀ {x y} → G .Edge x y → H .Edge (vertex x) (vertex y)
```

<!--
```agda
private variable
  G H K : Graph o ℓ

open Graph-hom

unquoteDecl H-Level-Graph-hom = declare-record-hlevel 2 H-Level-Graph-hom (quote Graph-hom)

Graph-hom-pathp
  : {G : I → Graph o ℓ} {H : I → Graph o' ℓ'}
  → {f : Graph-hom (G i0) (H i0)} {g : Graph-hom (G i1) (H i1)}
  → (p0 : ∀ (x : ∀ i → G i .Vertex)
          → PathP (λ i → H i .Vertex)
              (f .vertex (x i0)) (g .vertex (x i1)))
  → (p1 : ∀ {x y : ∀ i → G i .Vertex}
          → (e : ∀ i → G i .Edge (x i) (y i))
          → PathP (λ i → H i .Edge (p0 x i) (p0 y i))
              (f .edge (e i0)) (g .edge (e i1)))
  → PathP (λ i → Graph-hom (G i) (H i)) f g
Graph-hom-pathp {G = G} {H = H} {f = f} {g = g} p0 p1 = pathp where
  vertex* : I → Type _
  vertex* i = (G i) .Vertex

  edge* : (i : I) → vertex* i → vertex* i → Type _
  edge* i x y = (G i) .Edge x y

  pathp : PathP (λ i → Graph-hom (G i) (H i)) f g
  pathp i .vertex x = p0 (λ j → coe vertex* i j x) i
  pathp i .edge {x} {y} e =
    p1 {x = λ j → coe vertex* i j x} {y = λ j → coe vertex* i j y}
      (λ j → coe (λ j → edge* j (coe vertex* i j x) (coe vertex* i j y)) i j (e* j)) i
    where

      x* y* : (j : I) → vertex* i
      x* j = coei→i vertex* i x (~ j ∨ i)
      y* j = coei→i vertex* i y (~ j ∨ i)

      e* : (j : I) → edge* i (coe vertex* i i x) (coe vertex* i i y)
      e* j =
        comp (λ j → edge* i (x* j) (y* j)) ((~ i ∧ ~ j) ∨ (i ∧ j)) λ where
          k (k = i0) → e
          k (i = i0) (j = i0) → e
          k (i = i1) (j = i1) → e

Graph-hom-path
  : {f g : Graph-hom G H}
  → (p0 : ∀ x → f .vertex x ≡ g .vertex x)
  → (p1 : ∀ {x y} → (e : Graph.Edge G x y) → PathP (λ i → Graph.Edge H (p0 x i) (p0 y i)) (f .edge e) (g .edge e))
  → f ≡ g
Graph-hom-path {G = G} {H = H} p0 p1 =
  Graph-hom-pathp {G = λ _ → G} {H = λ _ → H}
    (λ x i → p0 (x i) i)
    (λ e i → p1 (e i) i)

instance
  Funlike-Graph-hom : Funlike (Graph-hom G H) ⌞ G ⌟ λ _ → ⌞ H ⌟
  Funlike-Graph-hom .Funlike._#_ = vertex

Graph-hom-id : {G : Graph o ℓ} → Graph-hom G G
Graph-hom-id .vertex v = v
Graph-hom-id .edge e = e

```
-->

Graphs and graph homomorphisms can be organized into a category $\Graphs$.

```agda
Graphs : ∀ o ℓ → Precategory (lsuc (o ⊔ ℓ)) (o ⊔ ℓ)
Graphs o ℓ .Precategory.Ob = Graph o ℓ
Graphs o ℓ .Precategory.Hom = Graph-hom
Graphs o ℓ .Precategory.Hom-set _ _ = hlevel 2
Graphs o ℓ .Precategory.id = Graph-hom-id
Graphs o ℓ .Precategory._∘_ f g .vertex v = f .vertex (g .vertex v)
Graphs o ℓ .Precategory._∘_ f g .edge e = f .edge (g .edge e)
Graphs o ℓ .Precategory.idr _ = Graph-hom-path (λ _ → refl) (λ _ → refl)
Graphs o ℓ .Precategory.idl _ = Graph-hom-path (λ _ → refl) (λ _ → refl)
Graphs o ℓ .Precategory.assoc _ _ _ = Graph-hom-path (λ _ → refl) (λ _ → refl)

module Graphs {o} {ℓ} = Cat.Reasoning (Graphs o ℓ)

module _ {o ℓ : Level} where
  open Cat.Morphism (Graphs o ℓ)
  Graphs-is-category : is-category (Graphs o ℓ)
  Graphs-is-category .to-path {G} {H} G≅H = p where
    module G≅H = _≅_ G≅H
    module G→H = Graph-hom G≅H.to
    module G←H = Graph-hom G≅H.from
    module G = Graph G
    module H = Graph H
    vert≃ : G.Vertex ≃ H.Vertex
    vert≃ = Iso→Equiv $ G→H.vertex , iso G←H.vertex (λ v i → G≅H.invl i .vertex v) λ v i → G≅H.invr i .vertex v
    edge≃ : ∀ {u v} → G.Edge u v ≃ H.Edge (G→H.vertex u) (G→H.vertex v)
    edge≃ = Iso→Equiv $ G→H.edge , iso {! !} {! !} {! !}
    p : G ≡ H
    p = Graph-path (ua vert≃) (ua→2 λ u v → ua $ edge≃)
  Graphs-is-category .to-path-over p = {! !}
```

the category $\Graphs$ is equivalent to the category of presheaves of
parallel arrows (equivalently: functors from the parallel arrow category).
```agda
module _ {ℓ : Level} where
  open Functor
  open Graph
  parallel-to-graph : Functor Cat[ ·⇉· , Sets ℓ ] (Graphs ℓ ℓ)
  parallel-to-graph .F₀ F = g
    where module F = Functor F
          g : Graph ℓ ℓ
          g .Vertex = ∣ F.₀ true ∣
          g .Edge s d = Σ[ e ∈ ∣ F.₀ false ∣ ]  F.₁ false e ≡ s × F.₁ true e ≡ d
          g .Vertex-is-set = hlevel 2
          g .Edge-is-set = hlevel 2
  parallel-to-graph .F₁ {F} {G} nt = hom
    where open _=>_ nt
          hom : Graph-hom _ _
          hom .vertex = η true
          hom .edge {x} {y} (e , pₛ , pₜ) = η false e
                                          , happly (sym (is-natural _ _ _)) e ∙ ap _ pₛ
                                          , happly (sym (is-natural _ _ _)) e ∙ ap _ pₜ
  parallel-to-graph .F-id {F}  = Graph-hom-path (λ _ → refl) (λ _  → Σ-prop-path! refl)
  parallel-to-graph .F-∘ η ε = Graph-hom-path (λ _ → refl) (λ _ → Σ-prop-path! refl)

  graph-to-parallel : Functor (Graphs ℓ ℓ) Cat[ ·⇉· , Sets ℓ ]
  graph-to-parallel .F₀ G = Fork {a = el! $ Σ[ s ∈ G .Vertex ] Σ[ d ∈ G .Vertex ] G .Edge s d } {el! $ G .Vertex} fst (fst ⊙ snd)
  graph-to-parallel .F₁ f = Fork-nt {t = λ (s , d , e) → f .vertex s , f .vertex d , f .edge e} {u = f .vertex } refl refl
  graph-to-parallel .F-id = Nat-path λ { true → refl ; false → refl }
  graph-to-parallel .F-∘ G H = Nat-path λ { true → refl ; false → refl }

  private
    module parallel-to-graph = Functor parallel-to-graph
    module graph-to-parallel = Functor graph-to-parallel

  parallel-to-graph-inv : ∀ G → parallel-to-graph.F₀ (graph-to-parallel.F₀ G) ≡ G
  parallel-to-graph-inv G = sym (Graph-path refl (λ i u v → Iso→Path (Σ-iso {u} {v}) i))
    where module G = Graph G
          open is-iso
          Σ-iso : ∀ {u v} → Iso (G.Edge u v) (Σ[ e ∈ Σ[ u' ∈ G.Vertex ] Σ[ v' ∈ G.Vertex ] G.Edge u' v' ] (fst e ≡ u) × (fst (snd e) ≡ v))
          Σ-iso {u} {v} .fst e = ( u , v , e ) , refl , refl
          Σ-iso {u} {v} .snd .inv (( u' , v' , e ) , pᵤ , pᵥ) = transport (λ i → G .Edge (pᵤ i) (pᵥ i)) e
          Σ-iso {u} {v} .snd .rinv (( u' , v' , e ) , p₁ , p₂) = Σ-prop-path! (Σ-pathp (sym p₁) (Σ-pathp (sym p₂) (to-pathp⁻ refl)))
          Σ-iso {u} {v} .snd .linv e = to-pathp⁻ refl

  graph-to-parallel-inv : ∀ F → graph-to-parallel.F₀ (parallel-to-graph.F₀ F) ≡ F
  graph-to-parallel-inv F = Functor-path p₀ p₁
    where module F = Functor F
          V = ∣ F.F₀ true ∣
          E = ∣ F.F₀ false ∣
          src =  F.F₁ false
          dst =  F.F₁ true

          open is-iso
          Σ-iso : Iso (Σ[ s ∈ V ] Σ[ d ∈ V ] Σ[ e ∈ E ] (src e ≡ s) × (dst e ≡ d)) E
          Σ-iso .snd .inv e = src e , dst e , e , refl , refl
          Σ-iso .fst (u , v , e , pᵤ , pᵥ) = e
          Σ-iso .snd .linv (u , v , e , pᵤ , pᵥ) =
            Σ-pathp pᵤ $ Σ-pathp pᵥ $ Σ-pathp refl $ is-prop→pathp (λ i → hlevel 1) (refl , refl) (pᵤ , pᵥ)
          Σ-iso .snd .rinv e = refl

          p₀ : (x : Bool) → (graph-to-parallel.F₀ (parallel-to-graph.F₀ F)) .F₀ x ≡ F.₀ x
          p₀ true = n-path refl
          p₀ false = n-path (Iso→Path Σ-iso)

          p₁ : ∀ {x y} (f : ·⇉·.Hom x y) → PathP (λ i → Precategory.Hom (Sets ℓ) (p₀ x i) (p₀ y i)) ((graph-to-parallel.F₀ (parallel-to-graph.F₀ F)) .F₁ {x} {y} f) (F.₁ f)
          p₁ {true} {true} _ = sym F.F-id
          p₁ {false} {true} true = ua→ λ { (_ , _ , _ , pᵤ , pᵥ) → sym pᵥ }
          p₁ {false} {true} false = ua→ λ { (_ , _ , _ , pᵤ , pᵥ) → sym pᵤ }
          p₁ {false} {false} _ = ua→ λ _ → path→ua-pathp _ (happly (sym F.F-id) _)

  private module _ where
    open Cat.Morphism using (Isomorphism)
    parallel-to-graph-iso : ∀ G → Isomorphism (Graphs ℓ ℓ) (parallel-to-graph.F₀ (graph-to-parallel.F₀ G)) G
    parallel-to-graph-iso G = path→iso $ parallel-to-graph-inv G

    graph-to-parallel-iso : ∀ F →  Isomorphism Cat[ ·⇉· , Sets ℓ ] (graph-to-parallel.F₀ (parallel-to-graph.F₀ F))  F
    graph-to-parallel-iso F = path→iso $ graph-to-parallel-inv F


{-
  graph-to-parallel⊣parallel-to-graph : graph-to-parallel ⊣ parallel-to-graph
  graph-to-parallel⊣parallel-to-graph = adjoint where
    open _⊣_
    open _=>_
    open Cat.Reasoning
    adjoint : graph-to-parallel ⊣ parallel-to-graph
    adjoint .unit .η G = parallel-to-graph-iso G .from
    adjoint .unit .is-natural G H f = Graph-hom-path (λ v → transport-refl _ ∙ transport-refl _ ∙ {! !}) (λ e → {! Σ-prop-path! ? !})
    adjoint .counit .η F = graph-to-parallel-iso F .to
    adjoint .counit .is-natural = ?
      where hom : Graph-hom _ _
            hom .vertex v = v
            hom .edge {u} {v} e = (u , v , e) , refl , refl
    adjoint .unit .is-natural x y f = Graph-hom-path (λ _ → refl ) (λ _ → Σ-prop-path! refl)
    adjoint .counit .η F = nt
      where module F = Functor F
            nt : _ => _
            nt .η true x = x
            nt .η false (_ , _ , x , _ , _) = x
            nt .is-natural true true _ = sym F.F-id
            nt .is-natural false true true i (_ , _ , _ , _ , p) = p (~ i)
            nt .is-natural false true false i (_ , _ , _ , p , _) = p (~ i)
            nt .is-natural false false _ i (_ , _ , e , _ , _)= F.F-id (~ i) e
    adjoint .counit .is-natural F G f = ext λ { true  x → refl
                                              ; false x → refl }
    adjoint .zig = ext λ { true  x → refl
                         ; false x → refl }
    adjoint .zag = Graph-hom-path (λ _ → refl ) (λ _ → Σ-prop-path! refl)
-}

{-
  open is-equivalence
  g2p-is-eqv : is-equivalence graph-to-parallel
  g2p-is-eqv .F⁻¹ = parallel-to-graph
  g2p-is-eqv .F⊣F⁻¹ = graph-to-parallel⊣parallel-to-graph
  g2p-is-eqv .unit-iso G = {! transport (λ i → {! !}) id-invertible !}
    where open Cat.Morphism (Graphs ℓ ℓ)
{-
          hom : Graph-hom _ _
          hom = transport (λ i → Graph-hom (parallel-to-graph-inv G (~ i)) G) Graph-hom-id
          open Cat.Morphism (Graphs _ _)
          open Inverses
          inv : Inverses _ _
          inv .invl = Graph-hom-path
            (λ v → transport-refl _ ∙ transport-refl _ )
            λ { ((u , v , e) , pᵤ , pᵥ) i → ( transp (λ _ → G.Vertex) i (transp (λ _ → G.Vertex) i (pᵤ (~ i)))
                                            , transp (λ _ → G.Vertex) i (transp (λ _ → G.Vertex) i (pᵥ (~ i)))
                                            , {! !}) , {! !} , {! !} }
         (λ i₁ →
            G.Edge
            (transp (λ i₂ → G.Vertex) (~ i₁)
             (transp (λ j → G.Vertex) (~ i₁) (transp (λ j → G.Vertex) i₁ x)))
            (transp (λ i₂ → G.Vertex) (~ i₁)
             (transp (λ j → G.Vertex) (~ i₁) (transp (λ j → G.Vertex) i₁ y))))
            where module G = Graph G
          inv .invr = Graph-hom-path (λ v → transport-refl _ ∙ transport-refl _ )
                                     λ e i → {! !}
-}
  g2p-is-eqv .counit-iso F = {! !}
-}
{-


  open is-precat-iso
  open is-iso
  g2p-is-iso : is-precat-iso graph-to-parallel
  --g2p-is-iso .has-is-ff = is-equivalence→is-ff _ g2p-is-eqv
  g2p-is-iso .has-is-ff {G} {H} = is-iso→is-equiv $ F₁-iso where
    open Precategory using (Hom)
    F₁-iso : is-iso (graph-to-parallel .F₁ {G} {H})
    F₁-iso .inv nt = transport (λ i → Graph-hom (parallel-to-graph-inv G i) (parallel-to-graph-inv H i)) (parallel-to-graph.F₁ nt)
    F₁-iso .rinv nt = ext λ { true _ → transport-refl _ ∙ ap (η true) (transport-refl _)
                            ; false x i → transport-refl {! !} i , transport-refl {! !} i , {! !} } where
      open _=>_ nt
    F₁-iso .linv f = Graph-hom-path (λ x → transport-refl _ ∙ ap (f .vertex) (transport-refl _))
                                    λ { {x} {y} e → {! !} }
  g2p-is-iso .has-is-iso = is-iso→is-equiv F₀-iso where
    F₀-iso : is-iso (graph-to-parallel .F₀)
    F₀-iso .inv = parallel-to-graph .F₀
    F₀-iso .rinv F = graph-to-parallel-inv F
    F₀-iso .linv G = parallel-to-graph-inv G
-}

{-
  graphs-are-functors : (Graphs ℓ ℓ) ≡ Cat[ ·⇉· , Sets ℓ ]
  graphs-are-functors = Precategory-path _ g2p-is-iso

  graphs-are-presheaves : (Graphs ℓ ℓ) ≡ PSh ℓ ·⇉·
  graphs-are-presheaves = graphs-are-functors ∙ p
    where p : Cat[ ·⇉· , Sets ℓ ] ≡ PSh ℓ ·⇉·
          p i = Cat[ ·⇇·≡·⇉· (~ i) , Sets ℓ ]
-}
```

<!--
```agda
open Functor
```
-->

:::{.definition #underlying-graph alias="underlying-graph-functor"}
Note that every [[strict category]] has an underlying graph, where
the vertices are given by objects, and edges by morphisms. Moreover,
functors between strict categories give rise to graph homomorphisms
between underlying graphs. This gives rise to a functor from the
[[category of strict categories]] to the category of graphs.
:::

```agda
Strict-cats↪Graphs : Functor (Strict-cats o ℓ) (Graphs o ℓ)
Strict-cats↪Graphs .F₀ (C , C-strict) .Vertex = Precategory.Ob C
Strict-cats↪Graphs .F₀ (C , C-strict) .Edge = Precategory.Hom C
Strict-cats↪Graphs .F₀ (C , C-strict) .Vertex-is-set = C-strict
Strict-cats↪Graphs .F₀ (C , C-strict) .Edge-is-set = Precategory.Hom-set C _ _
Strict-cats↪Graphs .F₁ F .vertex = F .F₀
Strict-cats↪Graphs .F₁ F .edge = F .F₁
Strict-cats↪Graphs .F-id = Graph-hom-path (λ _ → refl) (λ _ → refl)
Strict-cats↪Graphs .F-∘ F G = Graph-hom-path (λ _ → refl) (λ _ → refl)
```

The underlying graph functor is faithful, as functors are graph homomorphisms
with extra properties.

```agda
Strict-cats↪Graphs-faithful : is-faithful (Strict-cats↪Graphs {o} {ℓ})
Strict-cats↪Graphs-faithful p =
  Functor-path
    (λ x i → p i .vertex x)
    (λ e i → p i .edge e)
```
