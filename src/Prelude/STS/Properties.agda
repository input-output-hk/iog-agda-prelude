module Prelude.STS.Properties where

open import Prelude.Init hiding (map)
open import Prelude.STS
open import Relation.Binary.Core using (_⇒_)

private variable Γ S I : Type

module _ ⦃ ht : HasTransition Γ S I ⦄ where

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

  module _
    ⦃ _ : Computational _⊢_—[_]→_ ⦄
    (let compute∗      = Computational.compute      Computational∗
         decidable∗    = Computational.decidable    Computational∗
         completeness∗ = Computational.completeness Computational∗)
    where

    -- An equivalent version of `compute` for the reflexive-transitive closure
    compute∗′ : {γ : Γ} → S → List I → Maybe S
    compute∗′     s []       = just s
    compute∗′ {γ} s (i ∷ is) with compute {_⊢_—[_]→_ = _⊢_—[_]→_} {γ} s i
    ... | just s′ = compute∗′ {γ} s′ is
    ... | nothing = nothing

    compute∗′≡compute∗ : ∀ (s : S) (is : List I) → compute∗′ {γ} s is ≡ compute∗ {γ} s is
    compute∗′≡compute∗ {γ} s []       = refl
    compute∗′≡compute∗ {γ} s (i ∷ is) with compDec {γ = γ} s i
    ... | no _ = refl
    ... | yes (s′ , _) with decidable∗ {γ} s′ is
    ...   | yes (_ , π) rewrite compute∗′≡compute∗ {γ} s′ is | completeness∗ _ _ _ π            = refl
    ...   | no ¬π       rewrite compute∗′≡compute∗ {γ} s′ is | dec-no (decidable∗ {γ} s′ is) ¬π = refl

  -- A left-total STS and its reflexive-transitive closure are always decidable
  LeftTotal : {A : Type ℓ} {B : Type ℓ′} (R : REL A B ℓ″) → Type (ℓ ⊔ₗ ℓ′ ⊔ₗ ℓ″)
  LeftTotal R = ∀ x → ∃[ y ] R x y

  module _ (left-total : ∀ (i : I) → LeftTotal (γ ⊢_—[ i ]→_)) where
    left-total⇒decidable : ∀ (i : I) (s : S) → Dec $ ∃ (γ ⊢ s —[ i ]→_)
    left-total⇒decidable = yes ∘₂ left-total

    ∗-left-total : ∀ (is : List I) → LeftTotal (γ ⊢_—[ is ]→∗_)
    ∗-left-total []       s = s , []
    ∗-left-total (i ∷ is) s =
      let (s′ , π′) = left-total i s
          (s″ , π″) = ∗-left-total is s′
      in  s″ , π′ ∷ π″

  module _ where

    open Map ⦃ ht ⦄ ⦃ ht ⦄

    map-id : ∀ (ts∗ : γ ⊢ s —[ is ]→∗ s″) → map id ts∗ ≡ ts∗
    map-id []         = refl
    map-id (ts ∷ ts∗) = cong (_∷_ ts) (map-id ts∗)

module _ ⦃ ht₁ : HasTransition Γ S I ⦄ ⦃ ht₂ : HasTransition Γ S I ⦄ where

  open HasTransition ht₁ renaming (_⊢_—[_]→_ to _⊢_—[_]¹→_; _⊢_—[_]→∗_ to _⊢_—[_]¹→∗_)
  open HasTransition ht₂ renaming (_⊢_—[_]→_ to _⊢_—[_]²→_; _⊢_—[_]→∗_ to _⊢_—[_]²→∗_)
  open Map ⦃ ht₁ ⦄ ⦃ ht₂ ⦄
  open import Relation.Binary.PropositionalEquality using (cong₂)

  map-cong : ∀ {γ}
    (f : ∀ {i} → γ ⊢_—[ i ]¹→_ ⇒ γ ⊢_—[ i ]²→_) →
    (g : ∀ {i} → γ ⊢_—[ i ]¹→_ ⇒ γ ⊢_—[ i ]²→_) →
    (∀ {i s s″} (ts : γ ⊢ s —[ i ]¹→ s″) → f ts ≡ g ts) →
    ∀ {is s s″} (ts∗ : γ ⊢ s —[ is ]¹→∗ s″) →
    map f ts∗ ≡ map g ts∗
  map-cong f g eq []         = refl
  map-cong f g eq (ts ∷ ts∗) = cong₂ _∷_ (eq ts) (map-cong f g eq ts∗)

  module _ ⦃ ht₃ : HasTransition Γ S I ⦄ where

    open HasTransition ht₃ renaming (_⊢_—[_]→_ to _⊢_—[_]³→_; _⊢_—[_]→∗_ to _⊢_—[_]³→∗_)
    open Map ⦃ ht₂ ⦄ ⦃ ht₃ ⦄ renaming (map to map′)
    open Map ⦃ ht₁ ⦄ ⦃ ht₃ ⦄ renaming (map to map″)

    map-∘ : ∀ {γ : Γ} {s s″ : S} {is : List I}
      (f : ∀ {i} → γ ⊢_—[ i ]²→_ ⇒ γ ⊢_—[ i ]³→_)
      (g : ∀ {i} → γ ⊢_—[ i ]¹→_ ⇒ γ ⊢_—[ i ]²→_)
      (ts∗ : γ ⊢ s —[ is ]¹→∗ s″) →
      (map′ f ∘ map g) ts∗ ≡ map″ (f ∘ g) ts∗
    map-∘ f g []         = refl
    map-∘ f g (ts ∷ ts∗) = cong (_∷_ (f (g ts))) (map-∘ f g ts∗)
