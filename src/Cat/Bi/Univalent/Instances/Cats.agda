
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bi
import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr
import Cat.Univalent

open import Cat.Bi.Base

module Cat.Bi.Univalent.Instances.Cats (o ℓ : Level) where

open Prebicategory
Univalent-Cat : Prebicategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Univalent-Cat .Ob = Cat o ℓ .Ob
Univalent-Cat .Hom x x₁ = ?
Univalent-Cat .id = ?
Univalent-Cat .compose = ?
Univalent-Cat .unitor-l = ?
Univalent-Cat .unitor-r = ?
Univalent-Cat .associator = ?
Univalent-Cat .triangle f g = ?
Univalent-Cat .pentagon f g h i = ?
