{-# OPTIONS --safe #-}

module Class.Computational where

open import Agda.Primitive using () renaming (Set to Type)
open import Level

open import Prelude.Init hiding (map)

open import Class.Applicative
open import Class.Bifunctor
open import Class.DecEq
open import Class.Functor renaming (fmap to map)
open import Class.Monad
open import Class.Semigroup
open import Class.Show.Core
open import Function
open import Relation.Binary.PropositionalEquality

private variable
  a : Level
  I O : Type
  i : I
  o o' : O
  Err Err₁ Err₂ : Type

data ComputationResult {a : Level} (Err : Type) (R : Type a) : Type a where
  success : R → ComputationResult Err R
  failure : Err → ComputationResult Err R

isFailure : ∀ {A : Type a} → ComputationResult Err A → Type a
isFailure x = ∃[ e ] x ≡ failure e

module _ {a b} {E : Type} {A : Type a} {B : Type b} where
  caseCR_∣_∣_ : (ma : ComputationResult E A) → (∀ {a} → ma ≡ success a → B) → (isFailure ma → B) → B
  caseCR ma ∣ f ∣ g with ma
  ... | success _ = f refl
  ... | failure e = g (e , refl)

  caseCR-success : ∀ {a} {ma : ComputationResult E A} {f : ∀ {a} → ma ≡ success a → B} {g : isFailure ma → B}
    → (eq : ma ≡ success a)
    → caseCR ma ∣ f ∣ g ≡ f eq
  caseCR-success refl = refl

  caseCR-failure : {ma : ComputationResult E A} {f : ∀ {a} → ma ≡ success a → B} {g : isFailure ma → B}
    → (eq : isFailure ma)
    → caseCR ma ∣ f ∣ g ≡ g eq
  caseCR-failure (_ , refl) = refl

instance
  Bifunctor-ComputationResult : ∀ {a : Level} → Bifunctor {_} {a} ComputationResult
  Bifunctor-ComputationResult .bimap _ f (success x) = success $ f x
  Bifunctor-ComputationResult .bimap f _ (failure x) = failure $ f x

  Functor-ComputationResult : ∀ {E : Type} → Functor (ComputationResult E)
  Functor-ComputationResult ._<$>_ f (success x) = success $ f x
  Functor-ComputationResult ._<$>_ _ (failure x) = failure x

  Applicative-ComputationResult : ∀ {E : Type} → Applicative (ComputationResult E)
  Applicative-ComputationResult .pure = success
  Applicative-ComputationResult ._<*>_ (success f) x = f <$> x
  Applicative-ComputationResult ._<*>_ (failure e) _ = failure e

  Monad-ComputationResult : ∀ {E : Type} → Monad (ComputationResult E)
  Monad-ComputationResult .return = success
  Monad-ComputationResult ._>>=_ (success a) m = m a
  Monad-ComputationResult ._>>=_ (failure e) _ = failure e

  Show-ComputationResult : ∀ {l} {E : Type} {A : Type l} → ⦃ Show E ⦄ → ⦃ Show A ⦄ → Show (ComputationResult E A)
  Show-ComputationResult .show (success x) = "success " ◇ show x
  Show-ComputationResult .show (failure e) = "failure " ◇ show e

map-failure : ∀ {A B C : Type} {f : A → B} {x : C} {ma} → ma ≡ failure x → map f ma ≡ failure x
map-failure refl = refl

success-maybe : ∀ {R : Type} → ComputationResult Err R → Maybe R
success-maybe (success x) = just x
success-maybe (failure _) = nothing

failure-maybe : ∀ {R : Type} → ComputationResult Err R → Maybe Err
failure-maybe (success _) = nothing
failure-maybe (failure x) = just x

_≈ᶜʳ_ : ∀ {A} → ComputationResult Err A → ComputationResult Err A → Type
x ≈ᶜʳ y = success-maybe x ≡ success-maybe y

module _ (STS : I → O → Type) where

  ExtendedRel : I → ComputationResult Err O → Type
  ExtendedRel i (success o) = STS i o
  ExtendedRel i (failure _) = ∀ o → ¬ STS i o

  record Computational Err : Type₁ where
    constructor MkComputational
    field
      computeProof : (i : I) → ComputationResult Err (∃[ o ] STS i o)

    compute : I → ComputationResult Err O
    compute i = map proj₁ $ computeProof i

    field
      completeness : (i : I) → (o : O) → STS i o → compute i ≡ success o

    open ≡-Reasoning

    computeFail : I → Type
    computeFail i = isFailure $ compute i

    ≡-success⇔STS : compute i ≡ success o ⇔ STS i o
    ≡-success⇔STS {i} {o} with computeProof i in eq
    ... | success (o' , h) = mk⇔ (λ where refl → h) λ h' →
      begin success o' ≡˘⟨ completeness _ _ h ⟩
            compute i  ≡⟨ completeness _ _ h' ⟩
            success o  ∎
    ... | failure y = mk⇔ (λ ()) λ h →
      begin failure _ ≡˘⟨ map-failure eq ⟩
            compute i ≡⟨ completeness _ _ h ⟩
            success o ∎

    failure⇒∀¬STS : computeFail i → ∀ o → ¬ STS i o
    failure⇒∀¬STS comp≡nothing o h rewrite ≡-success⇔STS .Equivalence.from h =
      case comp≡nothing of λ ()

    ∀¬STS⇒failure : (∀ o → ¬ STS i o) → computeFail i
    ∀¬STS⇒failure {i = i} ¬sts with computeProof i
    ... | success (x , y) = ⊥-elim (¬sts x y)
    ... | failure y = (y , refl)

    failure⇔∀¬STS : computeFail i ⇔ ∀ o → ¬ STS i o
    failure⇔∀¬STS = mk⇔ failure⇒∀¬STS ∀¬STS⇒failure

    recomputeProof : STS i o → ComputationResult Err (∃[ o' ] STS i o')
    recomputeProof _ = computeProof _

module _ (STS : I → O → Type) ⦃ comp : Computational STS Err ⦄ where

  open Computational comp

  ExtendedRelSTS = ExtendedRel STS

  ExtendedRel-compute : ExtendedRelSTS i (compute i)
  ExtendedRel-compute {i} with compute i in eq
  ... | success o = Equivalence.to ≡-success⇔STS eq
  ... | failure _ = λ o h → case trans (sym $ Equivalence.from ≡-success⇔STS h) eq of λ ()

  open ≡-Reasoning

  ExtendedRel-rightUnique : ExtendedRelSTS i o → ExtendedRelSTS i o' → _≈ᶜʳ_ {Err = Err} o o'
  ExtendedRel-rightUnique {o = success x} {success x'} h h'
    with trans (sym $ Equivalence.from ≡-success⇔STS h) (Equivalence.from ≡-success⇔STS h')
  ... | refl = refl

  ExtendedRel-rightUnique {o = success x} {failure _}  h h' = ⊥-elim $ h' x h
  ExtendedRel-rightUnique {o = failure _} {success x'} h h' = ⊥-elim $ h x' h'
  ExtendedRel-rightUnique {o = failure a} {failure b}  h h' = refl

  computational⇒rightUnique : STS i o → STS i o' → o ≡ o'
  computational⇒rightUnique h h' with ExtendedRel-rightUnique h h'
  ... | refl = refl

  Computational⇒Dec : ⦃ _ : DecEq O ⦄ → Dec (STS i o)
  Computational⇒Dec {i} {o}
    with compute i | ExtendedRel-compute {i}
  ... | failure _ | ExSTS = no (ExSTS o)
  ... | success x | ExSTS with x ≟ o
  ... | no ¬p     = no  λ h → ¬p $ sym $ computational⇒rightUnique h ExSTS
  ... | yes refl  = yes ExSTS

module _ {STS : I → O → Type} (comp comp' : Computational STS Err) where

  open Computational comp  renaming (compute to compute₁)
  open Computational comp' renaming (compute to compute₂)

  compute-ext≡ : compute₁ i ≈ᶜʳ compute₂ i
  compute-ext≡ = ExtendedRel-rightUnique _ ⦃ comp ⦄
    (ExtendedRel-compute _ ⦃ comp ⦄) (ExtendedRel-compute _ ⦃ comp' ⦄)

open Computational ⦃...⦄

Computational⇒Dec' :
  {STS : I → O → Type} ⦃ comp : Computational STS Err ⦄ → Dec (∃[ o ] STS i o)
Computational⇒Dec' with computeProof _ in eq
... | success x = yes x
... | failure x = no λ (_ , h) → failure⇒∀¬STS (-, cong (map proj₁) eq) _ h

record InjectError Err₁ Err₂ : Type where
  field injectError : Err₁ → Err₂

open InjectError

instance
  InjectError-⊥ : InjectError ⊥ Err
  InjectError-⊥ = λ where
    .injectError ()

  InjectError-Id : InjectError Err Err
  InjectError-Id = λ where
    .injectError → id
