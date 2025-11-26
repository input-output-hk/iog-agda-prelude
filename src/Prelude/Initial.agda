{-# OPTIONS --safe #-}
module Prelude.Initial where

open import Prelude.Init

record HasInitial (A : Type ℓ) : Type (lsuc ℓ) where
  field Initial : A → Type
open HasInitial ⦃...⦄ public

