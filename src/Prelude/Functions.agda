module Prelude.Functions where

open import Prelude.Init
open import Class.DecEq

-- non-dependent function updating
_⟪_←_⟫ : ∀ {A B : Set} ⦃ _ : DecEq A ⦄ → (A → B) → A → B → (A → B)
f ⟪ x ← y ⟫ = λ x′ → if x′ ≡ᵇ x then y else f x′
