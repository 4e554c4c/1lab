```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Prelude
open import Cat.Instances.Dist
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Product

open import Data.Set.Coequaliser
open import Data.Dec.Base
open import Data.Maybe.Base
open import Data.Bool.Base
open import Data.Maybe.Properties
open import Data.Fin.Closure
open import Data.Fin.Finite
open import Cat.Functor.Naturality
open import Cat.Monoidal.Braided
open import Data.Fin.Properties
open import Data.Sum
open import Data.Fin.Base renaming (_≤_ to _≤f_; _<_ to _<f_)
open import Data.Nat.Base
open import Data.Nat.Order
open import Data.Nat.Properties
open import Data.Vec.Base
open import Data.List.Base
open import Cat.Monoidal.Base
open import Cat.Functor.Bifunctor
```
-->

```agda
module Cat.Instances.Dist.Properties where


module sum {n} {m} = Equiv (Finite-coproduct {n} {m})

open Dist
open make-natural-iso

private variable
  n m l n' m' : Nat
  ℓ : Level
  A : Type ℓ

--act : (t : ⟨ n ⟩→⟨ m ⟩) → (v : Vec A n) → (Fin m) → List A
--act t v k = {!!}

invs : (t : ⟨ n ⟩→⟨ m ⟩) → (Fin m) → List (Fin n)
invs {n = n} t k = filter (λ j →  Dec→Bool $ t · j ≡ᵢ? just k) (all-fin n)


{-
module _ where
  open Make-bifunctor
  open ⟨_⟩→⟨_⟩
  open F+-monotonic
  open From-lt-cases
  bb : Make-bifunctor {C = Dist} {D = Dist} {E = Dist}
  bb .F₀ n m = n + m
  bb .lmap {n} {m} {l} f .map k = [ sum.to ⊙ inl <∙> f .map , pure ⊙ sum.to ⊙ inr ] $ sum.from k
  bb .lmap {n} {m} {l} f .ascending j k lt = p j k lt where
    p : ∀ j k → j ≤f k → bb .lmap {n} {m} {l} f .map j ≲ bb .lmap {n} {m} {l} f .map k
    p j k lt with from-lt-cases {n} {l} j k lt
    p j k lt | ll j' k' w w' lt' rewrite w rewrite w' =  Map-≲ ( λ {x} {y} lt  →  to-inl {m = l} x y lt ) ( f .ascending _ _ lt' )
    p j k lt | lr j' k' w w'     rewrite w rewrite w' with f · j'
    p j k lt | lr j' k' w w' | nothing = n≲j
    p j k lt | lr j' k' w w' | just x =  j≲j $ <-weaken $ inl<inr {n = m} {m = l} x k'
    p j k lt | rr j' k' w w' lt' rewrite w rewrite w' =  j≲j $ to-inr j' k' lt'
  bb .rmap {n} {m} {l} g .map y =  [ pure ⊙ sum.to ⊙ inl , sum.to ⊙ inr <∙> g .map ] $ sum.from y
  bb .rmap {n} {m} {l} g .ascending j k lt with from-lt-cases {l} {n}  j k lt
  bb .rmap {n} {m} {l} g .ascending j k lt | ll j' k' w w' lt' rewrite w rewrite w' = j≲j $ to-inl {m = l} j' k' lt'
  bb .rmap {n} {m} {l} g .ascending j k lt | lr j' k' w w' rewrite w rewrite w' with g · k'
  bb .rmap {n} {m} {l} g .ascending j k lt | lr j' k' w w' | nothing = j≲n
  bb .rmap {n} {m} {l} g .ascending j k lt | lr j' k' w w' | just x = j≲j $ <-weaken $ inl<inr {n = l} {m = m} j' x
  bb .rmap {n} {m} {l} g .ascending j k lt | rr j' k' w w' lt' rewrite w rewrite w' =  Map-≲ (λ {x} {y} lt  → to-inr {n = l} x y lt) $ g .ascending _ _ lt'
  bb .lmap-id {n} {m} = ext λ k → p k where
   p : ∀ k → [ sum.to ⊙ inl <∙> id .map , just ⊙ sum.to ⊙ inr ] (sum.from {n} {m} k) ≡ just k
   p k with sum.from {n} {m} k in w
   ... | inl x = ap just $ sum.adjunctr $ sym $ Id≃path.to w
   ... | inr x = ap just $ sum.adjunctr $ sym $ Id≃path.to w

  bb .rmap-id {n} {m} = ext p where
   p : ∀ k → [ pure ⊙ sum.to ⊙ inl , sum.to ⊙ inr <∙> id .map ] (sum.from {m} {n} k) ≡ just k
   p k with sum.from {m} {n} k in w
   ... | inl x = ap just $ sum.adjunctr $ sym $ Id≃path.to w
   ... | inr x = ap just $ sum.adjunctr $ sym $ Id≃path.to w

  bb .lmap-∘ {n} {m} {l} {k} f g = ext p where
    p : ∀ j → bb .lmap {x = k} (f ∘ g) · j ≡ (bb .lmap f ∘ bb .lmap g) · j
    p j with (holds? $ j .lower < n)
    p j | yes a with g · (fin (j .lower) ⦃ a ⦄)
    p j | yes a  | nothing = refl
    p j | yes a  | just x = sym $ (ap [ _ , _ ] (sum.η {m} {k} $ inl x))
    p j | no ¬a =  sym $ ap [ _ , _ ] (sum.η {m} {k} $ inr $ fin (j .lower - n) ⦃  nlt→lt j ¬a  ⦄)

  bb .rmap-∘ {n} {m} {l} {k} f g = ext p  where
    p : ∀ j → bb .rmap {a = k} (f ∘ g) · j ≡ (bb .rmap f ∘ bb .rmap g) · j
    p j with (holds? $ j .lower < k)
    ... | yes a = sym $ (ap [ _ , _ ] (sum.η {k} {m} $ inl $ fin (j .lower) ⦃ a ⦄ ))
    ... | no ¬a with g · (fin (j .lower - k) ⦃  nlt→lt j ¬a ⦄)
    ... | nothing = refl
    ... | just x  = sym $ (ap [ _ , _ ] (sum.η {k} {m} $ inr x))

  bb .lrmap  {n} {m} {l} {k} f g = ext λ j → p j where
    p : ∀ j → (bb .lmap f ∘ bb .rmap g) · j ≡ (bb .rmap g ∘ bb .lmap f) · j
    p j with (holds? (j .lower < n))
    p j | yes a =
      let j' = fin (j .lower) ⦃ a ⦄ in
      [ sum.to ⊙ inl <∙> f .map , just ⊙ sum.to ⊙ inr ] (sum.from $ sum.to $ inl j')
      ≡⟨ ap [ _ , _ ] (sum.η $ inl j')  ⟩
      (sum.to ⊙ inl) <$> (f · j')
      ≡⟨  bind-intror ∙ fmap-bind {x = f · j'} ⟩
      ((f · j') >>= (pure ⊙ sum.to ⊙ inl))
      ≡⟨ ( ap ((f · j') >>=_) $ ext λ k → sym $ ap [ _ , _ ] (sum.η $ inl k)) ⟩
      ((f · j') >>= ([ just ⊙ sum.to ⊙ inl , sum.to ⊙ inr <∙> g .map ] ⊙ sum.from ⊙ sum.to ⊙ inl))
      ≡˘⟨ fmap-bind {x = f · j'} {f = sum.to ⊙ inl} ⟩
      ((sum.to ⊙ inl <$> (f · j')) >>= ([ just ⊙ sum.to ⊙ inl , sum.to ⊙ inr <∙> g .map ] ⊙ sum.from))
      ∎

    p j | no ¬a = let j' = fin (j .lower - n)  ⦃  nlt→lt j ¬a ⦄ in
        ((sum.to ⊙ inr <$> g .map j') >>= ([ sum.to ⊙ inl <∙> f .map , just ⊙ sum.to ⊙ inr ] ⊙ sum.from))
        ≡⟨ fmap-bind {x = g · j'} {f = sum.to ⊙ inr}  ⟩
        (g .map j' >>= [ sum.to ⊙ inl <∙> f .map , just ⊙ sum.to ⊙ inr ] ⊙ sum.from ⊙ sum.to ⊙ inr)
        ≡⟨ ( ap (g · j' >>=_) $ ext λ k →  ap [ _ , _ ] (sum.η {n = n} $ inr k) ) ⟩
        (g .map j' >>= pure ⊙ sum.to ⊙ inr)
        ≡˘⟨ bind-intror ∙ fmap-bind {x = g · j'} ⟩
         (sum.to ⊙ inr <$> g · j')
        ≡˘⟨  ap [ _ , _ ] $ sum.η {n = m} {m = l} $ inr $ j' ⟩
        [ just ⊙ sum.to ⊙ inl , sum.to ⊙ inr <∙> g .map ] (sum.from $ sum.to {m} {l} $ inr j')
        ∎
  open Monoidal-category hiding (_◀_ ; _▶_ ; _⊗_ ; _⊗₁_)

  open Bifunctor (make-bifunctor bb) using (_◀_ ; _▶_) renaming (F₀ to infixr 25 _⊗_ ; _◆_ to infix 25 _⊗₁_)

  Dist-monoidal : Monoidal-category Dist
  Dist-monoidal .-⊗- = make-bifunctor bb
  Dist-monoidal .Unit = 0
  Dist-monoidal .unitor-l = to-natural-iso (record where
        eta n = id
        inv n = id
        eta∘inv n = trivial!
        inv∘eta n = trivial!
        natural n m f = ext λ k → p f k) where
        p : ∀ {n m} (f :  ⟨ n ⟩→⟨ m ⟩) → (k : Fin n) →
          (sum.to {0} {m} ⊙ inr <$> f .map k) ≡ (f .map k >>= just)
        p f k with f .map k
        ... | nothing = refl
        ... | just x =  ap just $ to-zerol x
  Dist-monoidal .unitor-r = to-natural-iso (record where
        eta n = cast-id $ sym $ +-zeror n
        inv n = cast-id $ +-zeror n
        eta∘inv n = trivial!
        inv∘eta n = trivial!
        natural n m f = ext λ k →  p f k) where
        p : ∀ {n m} (f :  ⟨ n ⟩→⟨ m ⟩) → (k : Fin n) →
          (bb .lmap {n} {m} {0} f .map (subst Fin (sym $ +-zeror n) k)) ≡ ( f .map k >>= (cast-id $ sym $ +-zeror m) .map)
        p {n} f k@(fin _ ⦃ p ⦄) rewrite (decide-yes (holds? (k .lower < n)) p) with f · k
        ... | nothing = refl
        ... | just x  = refl
  Dist-monoidal .associator = to-natural-iso (record where
        eta (j , k , l) = cast-id $ sym $ +-associative j k l
        inv (j , k , l) = cast-id $ +-associative j k l
        eta∘inv n = trivial!
        inv∘eta n = trivial!
        natural (n , m , l) (n' , m' , l') (f , g , h) = ext λ k → p f g h k) where
        p : ∀ {n m l n' m' l'} (f  : ⟨ n ⟩→⟨ n' ⟩) (g  : ⟨ m ⟩→⟨ m' ⟩) (h  : ⟨ l ⟩→⟨ l' ⟩)
          → (k : Fin $ n + m + l)
          → ((f ⊗₁ (g ⊗₁ h)) ∘ (cast-id $ sym $ +-associative n m l)) · k
          ≡ ((cast-id $ sym $ +-associative n' m' l') ∘ ((f ⊗₁ g) ⊗₁ h)) · k
        p {n = n} {m} {l} {n'} {m'} {l'} f g h k with (holds? ( k .lower < n))
        ... | yes a 
          rewrite (decide-yes (holds? $ k .lower < n) a)
          -- this is really nonsense
          rewrite (decide-yes (holds? $ k .lower < n + m) $ ≤-trans a $ +-≤l n m)
          rewrite (decide-yes (holds? $ k .lower < n + m) $ ≤-trans a $ +-≤l n m)
          rewrite (decide-yes (holds? $ k .lower < n) a)
          rewrite (decide-yes (holds? $ k .lower < n) a)
          with (f · (fin (k .lower) ⦃ a ⦄))
        ... | nothing = refl
        ... | just x  = ap just $ fin-ap refl
        p {n = n} {m} {l} {n'} {m'} {l'} f g h k | no ¬a with (holds? $ k .lower < n + m)
        ... |  b = {!!}
        --  rewrite (decide-yes (holds? $ k .lower - n < m) $ {!!})
        --  rewrite (decide-yes (holds? $ k .lower - n < m) $ {!!})
        --  rewrite (decide-yes (holds? $ k .lower < n + m) $ b)
        --  rewrite (decide-no  (holds? $ k .lower < n) ¬a)
        --  with (g · (fin (k .lower - n) ⦃ nlt→lt (fin (k .lower) ⦃ b ⦄)  ¬a ⦄)) in w
        --... | nothing = {! w!}
        --... | just  x = {!!}
        --p {n = n} {m} {l} {n'} {m'} {l'} f g h k | no ¬a | no ¬b = {!!} 
        --... | yes a rewrite (decide-yes (holds? $ k .lower < n) a) rewrite (decide-yes (holds? $ k .lower < n + m) $ ≤-trans a $ +-≤l n m) = {!!}
        --... | yes a = {!!}
        -- ... with (holds? $ k < (n + m))

  --iso→isoⁿ (λ (j , k , l) → path→iso $ sym $ +-associative j k l) {! !}
  Dist-monoidal .triangle {n} {m} = ext λ k →  p k  where
    p : ∀ k → ((cast-id (+-zeror n) ◀ m) .map <=< (cast-id (+-associative n 0 m) .map)) k
      ≡ (n ▶ Δ-id) .map k
    p k with (holds? (k .lower < n))
    ... | yes a rewrite (decide-yes (holds? $ k .lower < (n + 0)) ( ≤-trans a $ +-≤l _ _)) = refl
    ... | no ¬a rewrite (decide-no (holds? $ k .lower < (n + 0)) (subst (λ j → ¬ k .lower < j) (sym $ +-zeror n) ¬a)) =
      ap just $ fin-ap $ ap (λ j → n + (k .lower - j)) $ +-zeror n
  Dist-monoidal .pentagon {n} {m} {k} {l} = ext λ j → p j where
     p : ∀ j → (((cast-id (+-associative n m k) ◀ l) .map) <=< ((cast-id (+-associative n (m + k) l) .map) <=< (n ▶ (cast-id (+-associative m k l) )) .map)) j
       ≡ ((cast-id (+-associative (n + m) k l) .map) <=< (cast-id (+-associative n m (k + l)) .map)) j
     p (fin j) with (holds? (j < n))
     ... | yes a rewrite (decide-yes (holds? $ j < (n + (m + k))) ( ≤-trans a $ +-≤l _ _)) = refl
     ... | no ¬a with (holds? (n + (j - n) < n + (m + k)))
     ... | yes b = ap just $ fin-ap $ monus-+l-inverse n _ $ ≤-from-not-< _ _ ¬a
     ... | no ¬b = ap just $ fin-ap $
            n + m + k + (n + (j - n) - (n + (m + k)))
              ≡⟨ ap (_+ ((n + (j - n)) - (n + (m + k)))) (sym $ +-associative n m k) ⟩
            n + (m + k) + (n + (j - n) - (n + (m + k)))
              ≡⟨ (monus-+l-inverse _ _ $ ≤-from-not-< _ _ ¬b) ⟩
            n + (j - n)
              ≡⟨ (monus-+l-inverse n _ $ ≤-from-not-< _ _ ¬a ) ⟩
            j
            ∎

open Monoidal-category Dist-monoidal

-}
