--open import Order.Total
open import 1Lab.Function.Embedding
open import 1Lab.Prelude

open import Data.Partial.Base
open import Data.Bool.Order
open import Data.Bool.Base
open import Data.Nat.Order

module blah where

ℕ = Nat

is-decreasing : (Nat → Bool) → Type
is-decreasing α = (i : Nat) → α (suc i) ≤ α i

ℕ∞ : Type
ℕ∞ = Σ[ α ∈ (Nat → Bool) ] is-decreasing α
∞ : ℕ∞
∞ .fst _ =  true
∞ .snd _ = lift _

0∞ : ℕ∞
0∞ .fst _ = false
0∞ .snd _ = lift _

s∞ : ℕ∞ → ℕ∞
s∞ κ .fst 0 = true
s∞ κ .fst (suc n) = κ .fst n
s∞ κ .snd 0 = true-≤ _
s∞ κ .snd (suc n) = κ .snd n

s≠0 : ∀ κ → s∞ κ ≠ 0∞
s≠0 κ p = true≠false $ happly (ap fst p) 0

s-inj : injective s∞
s-inj {κ} {ν} p = Σ-prop-path! λ i n → p i .fst (suc n)

ι : ℕ → ℕ∞
ι 0 = 0∞
ι (suc n) = s∞ (ι n)

ι-inj : injective ι
ι-inj {zero} {zero} _ = refl
ι-inj {zero} {suc y} p = absurd $ᵢ s≠0 _ (sym p)
ι-inj {suc x} {zero} p = absurd $ᵢ s≠0 _ p
ι-inj {suc x} {suc y} p = ap suc $ ι-inj $ s-inj p


foo : ℕ∞ → ↯ ℕ
foo κ .def .∣_∣ = (fibre ι κ)
foo κ .def .is-tr = injective→is-embedding (hlevel 2) _ ι-inj κ
foo κ .elt x = x .fst

bar : ↯ ℕ → ℕ∞
bar κ .fst i = {! !}

module blah (inv :


is-compact∙ : Type → Type
is-compact∙ X = (p : X → Bool) → Σ[ x₀ ∈ X ] (p x₀ ≡ true → (x : X) → p x ≡ true)

{-
↯ℕ-is-compact∙ : is-compact∙ (↯ ℕ)
↯ℕ-is-compact∙ p .fst .def .∣_∣ = ∀ n →  p n ≡ true
↯ℕ-is-compact∙ p .fst .def .is-tr = hlevel 1
↯ℕ-is-compact∙ p .fst .elt q = 0
↯ℕ-is-compact∙ p .snd q x = {! ↯ℕ-is-compact∙ p .fst .def .∣_∣ !}
-}

↯ℕ-is-compact∙ : is-compact∙ (↯ ℕ)
↯ℕ-is-compact∙ p .fst .def .∣_∣ = minimal-solution λ n → (p (always n) ≡ false)
↯ℕ-is-compact∙ p .fst .def .is-tr = minimal-solution-unique {P = λ n → el _ (hlevel 1)}
↯ℕ-is-compact∙ p .fst .elt (n , _) = n
↯ℕ-is-compact∙ p .snd q x = {! !}
