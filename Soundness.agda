module Soundness where


open import Relation.Nullary.Negation
open import Data.Sum
open import Data.Product

open import Base
open import Subst
open import Semantics
open import Progress
open import Preservation

-- Let's put progress and preservation together to prove the main soundness theorem:
data Stuck (t : CTerm) : Set where
  is-stuck : ¬ (∃[ t' ](t ~> t')) → ¬ value t → Stuck t

-- Need to define transitive closure of ~>
data _~>*_ : CTerm → CTerm → Set where
  ~>-refl : ∀ {t : CTerm} → t ~>* t
  ~>-trans : ∀ {x y z : CTerm} → x ~> y → y ~>* z → x ~>* z


-- Here is the main soundness result.
-- A well-typed term t will never reach a Stuck state.
soundness : ∀ {t t' T} →
  ⊢ t ∈ T →
  t ~>* t' →
  ¬ (Stuck t')
soundness {t} {.t} {T} Ht ~>-refl (is-stuck ¬nf ¬val) with progress T t Ht
... | inj₁ val-t = ¬val val-t
... | inj₂ t'-step = ¬nf t'-step
soundness {t} {t'} {T} Ht (~>-trans {.t} {y} {.t'} t~>y y~>*t') =
  soundness (preservation Ht t~>y) y~>*t'
