module Semantics where

open import Base
open import Subst

-- Operational semantics
data value : {Γ : Context} → Term Γ → Set where
  val-lambda : ∀ {Γ A} → (t : Term (Γ , A)) → value (ƛ {Γ} {A} t)

infix 15 _~>_
-- data _~>_ : {Γ : Context} → Term Γ → Term Γ → Set where
--   step-lambda : ∀ {Γ A v} {t : Term (Γ , A)} →
--     value v →
--     (ƛ t $ v) ~> (t [ v ])
--   step-app1 : ∀ {Γ} {s s' t : Term Γ} →
--     s ~> s' →
--     s $ t ~> s' $ t
--   step-app2 : ∀ {Γ} {v t t' : Term Γ} →
--     value v →
--     t ~> t' →
--     v $ t ~> v $ t'

-- Do we need the relation to be indexed over Γ or can we just define it
-- for closed terms?
data _~>_ : CTerm → CTerm → Set where
  step-lambda : ∀ {A v} {t : Term (∅ , A)} →
    value v →
    (ƛ t $ v) ~> (t [ v ])
  step-app1 : ∀ {s s' t : CTerm} →
    s ~> s' →
    s $ t ~> s' $ t
  step-app2 : ∀ {v t t' : CTerm} →
    value v →
    t ~> t' →
    v $ t ~> v $ t'
