{-# OPTIONS --allow-unsolved-metas #-}


module Deterministic where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Subst hiding (S_)
open import Semantics


~>-deterministic : ∀ {s t₁ t₂} →
  s ~> t₁ →
  s ~> t₂ →
  t₁ ≡ t₂
~>-deterministic = {!!}
