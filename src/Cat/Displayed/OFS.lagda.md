<!--
```agda
open import Cat.Displayed.Base
open import Cat.Prelude

open import Cat.Morphism.Class
open import Cat.Morphism.Factorisation
open import Cat.Morphism.Factorisation.Orthogonal

import Cat.Displayed.Reasoning as Dr
import Cat.Reasoning as Cr
import Cat.Displayed.Solver as Ds
```
-->

```agda
module Cat.Displayed.OFS
  {o ℓ ℓl ℓr} {B : Precategory o ℓ} (b-cat : is-category B) (L : Arrows B ℓl) (R : Arrows B ℓr) (ofs : is-ofs B L R) where

open Cr B
open is-ofs ofs

variable
  o' ℓ' : Level
  a b c d : Ob
  --a' b' c' d' : Ob[ a ]

record Make-ofs-displayed : Type (o ⊔ ℓ ⊔ ℓl ⊔ ℓr ⊔ lsuc o' ⊔ lsuc ℓ') where
  field
      Ob[_] : Ob → Type o'
      L[_,_] : (f : Hom a b) → f ∈ L → Ob[ a ] → Ob[ b ] → Type ℓ'
      L[_,_]-set
        : (f : Hom a b) → (inl : f ∈ L) → (a' : Ob[ a ]) → (b' : Ob[ b ])
        → is-set (L[ f , inl ] a' b') 
      R[_,_] : (f : Hom a b) → f ∈ R → Ob[ a ] → Ob[ b ] → Type ℓ'
      R[_,_]-set
        : (f : Hom a b) → (inr : f ∈ R) → (a' : Ob[ a ]) → (b' : Ob[ b ])
        → is-set (R[ f , inr ] a' b') 
      idL : ∀ {a} {x : Ob[ a ]} → L[ id ,  id∈L ] x x
      idR : ∀ {a} {x : Ob[ a ]} → R[ id ,  id∈R ] x x
      _∘L_
        : ∀ {a' b' c'} {f : Hom b c} {g : Hom a b} {fL : f ∈ L} {gL : g ∈ L}
        → L[ f , fL ] b' c' → L[ g , gL ] a' b' → L[ f ∘ g , L-is-stable _ _ fL gL ] a' c'
      _∘R_
        : ∀ {a' b' c'} {f : Hom b c} {g : Hom a b} {fR : f ∈ R} {gR : g ∈ R}
        → R[ f , fR ] b' c' → R[ g , gR ] a' b' → R[ f ∘ g , R-is-stable _ _ fR gR ] a' c'
      -- ....

  open Displayed renaming (Ob[_] to O[_])
  open Factorisation
  make-displayed-ofs : Displayed B o' _
  make-displayed-ofs .O[_]  = Ob[_]
  make-displayed-ofs .Hom[_] f a' b' =
    Σ[ m' ∈ Ob[ f.mid ] ] L[ f.left , f.left∈L ] a'  m' × R[ f.right , f.right∈R ] m'  b'
    where module f = Factorisation (f .factor)
  make-displayed-ofs .id' {x} {x'} = transport (λ i → Ob[  f1≡f2 i .mid ])  x'
    , transport (λ i → L[ f1≡f2 i .left , f1≡f2 i .left∈L ]
                         x'
                         ((transp (λ j → Ob[ f1≡f2 (j ∧ i) .mid ]) (~ i) x')))
                idL
    , transport (λ i → R[ f1≡f2 i .right , f1≡f2 i .right∈R ]
                         ((transp (λ j → Ob[ f1≡f2 (j ∧ i) .mid ]) (~ i) x'))
                         x')
                idR
    where
      id-fact = id {x} .factor
      module id-fact = Factorisation id-fact
      id-fact' : Factorisation B L R id 
      id-fact' .mid = x
      id-fact' .left = id
      id-fact' .right = id
      id-fact' .left∈L = id∈L
      id-fact' .right∈R = id∈R
      id-fact' .factors =  sym $ idr _

      f1≡f2 : id-fact' ≡ id-fact 
      f1≡f2 =  factorisation-unique B L R ofs id b-cat _ _ 
  make-displayed-ofs ._∘'_ {a} {b} {c} {a'} {b'} {c'} {f} {g} f' g' = {!!} , {!!} , {!!}
      where
      module f = Factorisation (f .factor)
      module g = Factorisation (g .factor)
      fg1  = (f ∘ g) .factor
      r∘l : Hom g.mid f.mid
      r∘l = f.left ∘ g.right  
      module f1 = Factorisation fg1
      module r∘l = Factorisation (r∘l .factor)
      f2 : Factorisation B L R (f ∘ g)
      f2 .mid =  r∘l.mid
      f2 .left =  r∘l.left ∘ g.left
      f2 .right = f.right ∘ r∘l.right 
      f2 .left∈L = L-is-stable _ _ r∘l.left∈L g.left∈L
      f2 .right∈R =  R-is-stable _ _ f.right∈R r∘l.right∈R
      f2 .factors = {! !}


```
