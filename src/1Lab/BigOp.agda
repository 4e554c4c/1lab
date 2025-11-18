open import 1Lab.Type

module 1Lab.BigOp {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (_*_ : A → B → B) (unit : B)  where


private 
  O[_] : Nat → (Nat → A) → B
  O[ 0 ] f = unit
  O[ n@(suc m) ] f = f n * O[ m ] f

module Summation where
  ∑[_] = O[_]

module Product where
  ∏[_] = O[_]

module Coprod where
  ∐[_] = O[_]
