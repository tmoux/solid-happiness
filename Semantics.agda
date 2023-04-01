module Semantics where

open import Base
open import Subst

-- Operational semantics
data value : {Γ : Context} → Term Γ → Set where
  val-lambda : ∀ {Γ A} → (t : Term (Γ , A)) → value (ƛ {Γ} {A} t)

infix 15 _~>_ _~>*_
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

-- Need to define reflexive/transitive closure of ~>
data _~>*_ : CTerm → CTerm → Set where
  ~>-refl : ∀ {t : CTerm} → t ~>* t
  ~>-trans : ∀ {x y z : CTerm} → x ~> y → y ~>* z → x ~>* z


~>→~>* : ∀ {x y} → x ~> y → x ~>* y
~>→~>* s = ~>-trans s ~>-refl

~>*-trans : ∀ {x y z} → x ~>* y → y ~>* z → x ~>* z
~>*-trans ~>-refl y~>*z = y~>*z
~>*-trans (~>-trans x a) y~>*z = ~>-trans x (~>*-trans a y~>*z)

step-cong : ∀ {f s s'} → value f → s ~>* s' → f $ s ~>* f $ s'
step-cong val-f ~>-refl = ~>-refl
step-cong val-f (~>-trans s~>y y~>*s') = ~>-trans (step-app2 val-f s~>y) (step-cong val-f y~>*s')


module _ where
  open import Relation.Nullary.Negation

  value-is-nf : ∀ {t v} → value v → ¬ (v ~> t)
  value-is-nf {v = .(ƛ t)} (val-lambda t) ()
