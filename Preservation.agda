module Preservation where

open import Base
open import Subst
open import Semantics

preservation : ∀ {t t' T} →
  ⊢ t ∈ T →
  t ~> t' →
  ⊢ t' ∈ T
preservation {.(ƛ t $ x)} {.(t [ x ])} {T} (t-app {_} {S} {T} {ƛ {_} {.S} t} {x} (t-lambda t∈T) x∈S) (step-lambda val-x) =
  subst-lemma t∈T x∈S
preservation {.(f $ x)} {.(_ $ x)} {T} (t-app {S = S} {f = f} {x = x} f∈S⇒T x∈S) (step-app1 {_} {.f} {f'} tt) =
  let f'∈S⇒T = preservation f∈S⇒T tt
  in t-app f'∈S⇒T x∈S
preservation {.(ƛ t $ x)} {.(ƛ t $ _)} {T} (t-app {S = S} {f = .(ƛ t)} {x = x} f∈S⇒T x∈S) (step-app2 {_} {_} {x'} (val-lambda t) x~>x') =
  let x'∈S = preservation x∈S x~>x'
  in t-app f∈S⇒T x'∈S

preservation-multi : ∀ {t t' T} →
  ⊢ t ∈ T →
  t ~>* t' →
  ⊢ t' ∈ T
preservation-multi ⊢t ~>-refl = ⊢t
preservation-multi ⊢t (~>-trans t~>y y~>*t') = preservation-multi (preservation ⊢t t~>y) y~>*t'
