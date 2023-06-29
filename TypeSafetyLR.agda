module TypeSafetyLR where

open import Relation.Nullary.Negation
open import Data.Sum
open import Data.Product

open import Base
open import Subst
open import Semantics
open import Deterministic

𝓥⟦_⟧ : Typ → cvalue → Set
𝓥⟦ τ ⟧ = ?

data Stuck (t : CTerm) : Set where
  is-stuck : ¬ (∃[ t' ](t ~> t')) → ¬ value t → Stuck t

-- soundness : ∀ {t t' T} →
--   ⊢ t ∈ T →
--   t ~>* t' →
--   ¬ (Stuck t')
-- soundness = {!!}
