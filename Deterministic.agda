module Deterministic where

open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Base
open import Subst
open import Semantics


-- A very fun and interesting proof!
~>-deterministic : ∀ {Γ} {s t₁ t₂ : Term Γ} →
  s ~> t₁ →
  s ~> t₂ →
  t₁ ≡ t₂
~>-deterministic (step-lambda x) (step-lambda x₁) = refl
~>-deterministic (step-lambda val-v) (step-app2 x₁ s~>t₂) = ⊥-elim (value-is-nf val-v s~>t₂)
~>-deterministic (step-app1 s~>s') (step-app1 s~>s'') = Eq.cong (λ z → z $ _) (~>-deterministic s~>s' s~>s'')
~>-deterministic (step-app1 s~>s') (step-app2 val-s s~>t₂) = ⊥-elim (value-is-nf val-s s~>s') 
~>-deterministic (step-app2 val-v t~>t') (step-lambda val) = ⊥-elim (value-is-nf val t~>t')
~>-deterministic (step-app2 val-v t~>t') (step-app1 t~>t'') = ⊥-elim (value-is-nf val-v t~>t'')
~>-deterministic (step-app2 val-v t~>t') (step-app2 x t~>t'') = Eq.cong (λ z → _ $ z) (~>-deterministic t~>t' t~>t'')

-- Confluence is an easy consequence:
confluence : ∀ {Γ} {t u v : Term Γ} →
  t ~>* u →
  t ~>* v →
  ∃[ z ](u ~>* z × v ~>* z)
confluence {v = v} ~>-refl t~>*v = v , t~>*v , ~>-refl
confluence {u = u} t~>*u ~>-refl = u , ~>-refl , t~>*u
confluence {u = u} {v = v} (~>-trans {y = y} t~>y y~>*u) (~>-trans {y = y'} t~>y' y'~>*v) =
  confluence y~>*u (Eq.subst (λ z → z ~>* v) Hy y'~>*v)
  where
    Hy : y' ≡ y
    Hy = ~>-deterministic t~>y' t~>y
