module Prelude.STS.Properties where

open import Prelude.Init
open import Prelude.STS

private variable Γ S I : Type

module _ ⦃ _ : HasTransition Γ S I ⦄ where

  private variable
    γ : Γ
    s s′ s″ : S
    i : I
    is : List I

  —[[]]→∗⇒≡ : γ ⊢ s —[ [] ]→∗ s′ → s ≡ s′
  —[[]]→∗⇒≡ [] = refl

  ≡⇒—[[]]→∗ : s ≡ s′ → γ ⊢ s —[ [] ]→∗ s′
  ≡⇒—[[]]→∗ refl = []

  —[i]→⇒—[[i]]→∗ : γ ⊢ s —[ i ]→ s′ → γ ⊢ s —[ L.[ i ] ]→∗ s′
  —[i]→⇒—[[i]]→∗ p = p ∷ []

  —[∷ʳ]→∗-join : γ ⊢ s —[ is ]→∗ s″ → γ ⊢ s″ —[ i ]→ s′ → γ ⊢ s —[ is L.∷ʳ i ]→∗ s′
  —[∷ʳ]→∗-join []       q = —[i]→⇒—[[i]]→∗ q
  —[∷ʳ]→∗-join (p ∷ ps) q = p ∷ —[∷ʳ]→∗-join ps q

  —[∷ʳ]→∗-split : γ ⊢ s —[ is L.∷ʳ i ]→∗ s′ → ∃[ s″ ] γ ⊢ s —[ is ]→∗ s″ × γ ⊢ s″ —[ i ]→ s′
  —[∷ʳ]→∗-split {s = s} {is = []} (p ∷ ps) = s , [] , subst _ (—[[]]→∗⇒≡ ps) p
  —[∷ʳ]→∗-split {is = _ ∷ _} (p ∷ ps) with —[∷ʳ]→∗-split ps
  ... | (s″ , ps″ , p″) = (s″ , p ∷ ps″ , p″)

  —[[]]→∗ʳ⇒≡ : γ ⊢ s —[ [] ]→∗ʳ s′ → s ≡ s′
  —[[]]→∗ʳ⇒≡ [] = refl
  —[[]]→∗ʳ⇒≡ (_∷ʳ_ {eq = eq} _ _) = contradiction eq []≢∷ʳ
    where
      []≢∷ʳ : [] ≢ is L.∷ʳ i
      []≢∷ʳ {is = []}    ()
      []≢∷ʳ {is = _ ∷ _} ()

  ≡⇒—[[]]→∗ʳ : s ≡ s′ → γ ⊢ s —[ [] ]→∗ʳ s′
  ≡⇒—[[]]→∗ʳ refl = []

  —[]→∗⇒—[]→∗ʳ : γ ⊢ s —[ is ]→∗ s′ → γ ⊢ s —[ is ]→∗ʳ s′
  —[]→∗⇒—[]→∗ʳ {is = is} = —[]→∗⇒—[]→∗ʳ′ (reverseView is)
    where
      open import Data.List.Reverse
      —[]→∗⇒—[]→∗ʳ′ : ∀ {γ : Γ} {s s′ : S} {is : List I} → Reverse is → γ ⊢ s —[ is ]→∗ s′ → γ ⊢ s —[ is ]→∗ʳ s′
      —[]→∗⇒—[]→∗ʳ′ [] = ≡⇒—[[]]→∗ʳ ∘ —[[]]→∗⇒≡
      —[]→∗⇒—[]→∗ʳ′ (_ ∶ isr ∶ʳ _) ps with —[∷ʳ]→∗-split ps
      ... | (s″ , ps″ , p″) = _∷ʳ_ {eq = refl} (—[]→∗⇒—[]→∗ʳ′ isr ps″) p″

  —[]→∗ʳ⇒—[]→∗ : γ ⊢ s —[ is ]→∗ʳ s′ → γ ⊢ s —[ is ]→∗ s′
  —[]→∗ʳ⇒—[]→∗ [] = []
  —[]→∗ʳ⇒—[]→∗ (_∷ʳ_ {eq = eq} ps p) = subst _ (sym eq) (—[∷ʳ]→∗-join (—[]→∗ʳ⇒—[]→∗ ps) p)
