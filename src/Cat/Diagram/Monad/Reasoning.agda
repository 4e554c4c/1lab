open import Cat.Diagram.Monad using (Monad)

import Cat.Reasoning
open import Cat.Base using (Precategory)

import Cat.Functor.Reasoning
module Cat.Diagram.Monad.Reasoning {o ℓ} {𝒞 : Precategory o ℓ} (ℳ : Monad 𝒞) where

open Monad ℳ public
open Cat.Functor.Reasoning M hiding (op; ₀; ₁) public
