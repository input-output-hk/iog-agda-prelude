-- Properties for association lists
module Prelude.AssocList.Properties where

open import Class.DecEq
open import Class.Default
open import Prelude.AssocList
open import Prelude.Init

module _ {K V : Type} ⦃ _ : DecEq K ⦄ ⦃ _ : Default V ⦄ where

  private variable
    k k' : K
    v v' : V
    m : AssocList K V

  postulate -- TODO
    get∘set≡id : set k v m ⁉ k ≡ just v
    k'≢k-set-irrelevant : k' ≢ k → set k' v m ⁉ k ≡ m ⁉ k
    k'≢k-set-order : k' ≢ k → set k v (set k' v' m) ≡ set k' v' (set k v m)
