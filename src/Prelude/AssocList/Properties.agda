module Prelude.AssocList.Properties where

open import Class.DecEq
open import Class.Decidable using (¿_¿²)
open import Prelude.Init
open import Prelude.AssocList
open import Prelude.Irrelevance using (·¬⇒¬)

private variable
  K V : Type

module _ ⦃ _ : DecEq K ⦄ where

  private variable
    m : AssocList K V
    k : K
    v : V

  ------------------------------------------------------------------------
  -- ‼ and ⁉

  map-‼ : ∀ {ks : List K} → (p : k ∈ᵐ map (_, v) ks) → map (_, v) ks ‼ p ≡ v
  map-‼ {ks = _ ∷ _} First.[ refl ] = refl
  map-‼ {ks = _ ∷ _} (_ ∷ p)        = map-‼ p

  ⁉⇒‼ : m ⁉ k ≡ just v → Σ[ p ∈ k ∈ᵐ m ] m ‼ p ≡ v
  ⁉⇒‼ {m = m} {k = k} eq with k ∈ᵐ? m
  ... | yes First.[ refl ] = First.[ refl ] , M.just-injective eq
  ... | yes (x ∷ p) = x ∷ p , M.just-injective eq

  ‼⇒⁉ : ∀ (p : k ∈ᵐ m) → m ‼ p ≡ v → m ⁉ k ≡ just v
  ‼⇒⁉ {k = k} {m = m} {v = v} p eq with k ∈ᵐ? m | p
  ... | yes First.[ refl ] | First.[ refl ] = cong just eq
  ... | yes (≢k ∷ _)       | First.[ refl ] = contradiction refl (·¬⇒¬ ≢k)
  ... | yes First.[ refl ] | ≢k ∷ _         = contradiction refl (·¬⇒¬ ≢k)
  ... | yes (_ ∷ p)        | _ ∷ p′
        rewrite ∈ᵐ-irrelevant p p′          = cong just eq
  ... | no p               | q              = contradiction q p
