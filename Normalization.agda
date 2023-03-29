module Normalization where


open import Data.Sum
open import Data.Product
open import Function.Equivalence
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Base hiding (S_)
open import Subst
open IdSubst
open import Semantics
open import Progress
open import Preservation
open import Soundness

halts : CTerm → Set
halts t = ∃[ t' ](t ~>* t' × value t')

-- For a type T, the predicate (R T) represents the _reducibility candidates_
-- of type T, i.e., the (closed) terms of type T that halt, and when halting terms
-- are applied to it, also produce halting terms.
--
-- To prove normalization, it suffices to show that any reducibility candidate halts (trivial),
-- and that any closed term is a reducibility candidate.

R : Typ → CTerm → Set
R ⊤ t = (⊢ t ∈ ⊤) × halts t
R (A ⇒ B) f = (⊢ f ∈ A ⇒ B) × halts f × (∀ s → ⊢ s ∈ A → R A s → R B (f $ s))

R-halts : ∀ {T t} → R T t → halts t
R-halts {⊤} H = proj₂ H
R-halts {T ⇒ T₁} H = proj₁ (proj₂ H)


step-preserves-halt : ∀ {t t'} → (t ~>* t') → (halts t → halts t') × (halts t' → halts t)
step-preserves-halt = {!!}


R-app1 : ∀ {T f f' s} →
  f ~> f' →
  R T (f $ s) →
  R T (f' $ s)
R-app1 = {!!}


-- R is invariant under reduction.

R-step : ∀ {T t t'} → (t ~>* t') → R T t → R T t'
R-step {T} {t} {.t} ~>-refl H = H
R-step {⊤} {t} {t'} (~>-trans {y = y} t->y y->*t') (t∈⊤ , t-halts) =
  let y∈⊤ = preservation t∈⊤ t->y
      y-halts = proj₁ (step-preserves-halt {t} {y} (~>-trans t->y ~>-refl)) t-halts
      Ry : R ⊤ y
      Ry = y∈⊤ , y-halts
  in R-step {T = ⊤} y->*t' Ry
R-step {S ⇒ T} {t} {t'} (~>-trans {y = y} t->y y->*t) (t∈S⇒T , t-halts , Rs) =
  let y∈S⇒T = preservation t∈S⇒T t->y
      y-halts = proj₁ (step-preserves-halt {t} {y} (~>-trans t->y ~>-refl)) t-halts
      in let Ry : R (S ⇒ T) y
             Ry = y∈S⇒T , y-halts , λ s H₁ H₂ → R-app1 t->y (Rs s H₁ H₂)
      in R-step {T = S ⇒ T} y->*t Ry

R-step' : ∀ {T t t'} → ⊢ t ∈ T → (t ~> t') → R T t' → R T t
R-step' = {!!}

R-multistep' : ∀ {T t t'} → ⊢ t ∈ T → (t ~>* t') → R T t' → R T t
R-multistep' = {!!}


R-subst : ∀ {Γ T t} →
  (σ : ∀ {A} → Γ ∋ A → CTerm) →
  (∀ {A} → (x : Γ ∋ A) → ⊢ (σ x) ∈ A × value (σ x) × R A (σ x)) →
  Γ ⊢ t ∈ T →
  R T (subst σ t)
-- R-subst-id : ∀ {T t} →
--   ⊢ t ∈ T →
--   R T t
-- R-subst-id {T} {t} ⊢t = Eq.subst (λ z → R T z) (id-subst-id t) (R-subst {Γ = ∅} id-subst (λ ()) ⊢t)

R-subst σ Hσ (t-var x) = proj₂ (proj₂ (Hσ x))
R-subst σ Hσ (t-app {S = S} {T = T} {f = f} {x = x} ⊢f ⊢x) =
  let Rf : R (S ⇒ T) (subst σ f)
      Rf = R-subst σ Hσ ⊢f
      Rx : R S (subst σ x)
      Rx = R-subst σ Hσ ⊢x
  in proj₂ (proj₂ Rf) (subst σ x) (substs-lemma σ (λ x₁ → proj₁ (Hσ x₁)) ⊢x) Rx
R-subst σ Hσ (t-lambda {Γ = Γ} {S = S} {T = T} {t = t} ⊢t) =
                   ⊢λ
                 , (ƛ (subst (exts σ) t) , ~>-refl , val-lambda (subst (exts σ) t))
                 , Hs
  where ⊢λ : ⊢ ƛ (subst (exts σ) t) ∈ S ⇒ T
        ⊢λ = substs-lemma σ (λ x → proj₁ (Hσ x)) (t-lambda ⊢t)
        Hs : (s : CTerm) → ⊢ s ∈ S → R S s → R T (ƛ (subst (exts σ) t) $ s)
        Hs s ⊢s Rs with R-halts Rs
        ... | v , s~>*v , val-v =
          let ⊢v : ⊢ v ∈ S
              ⊢v = preservation-multi ⊢s s~>*v
              ss : CTerm
              ss = ƛ (subst (exts σ) t) $ s
              ss' : CTerm
              ss' = subst (exts σ) t [ v ]
              ss~>ss' : ss ~>* ss'
              ss~>ss' = ~>*-trans {y = ƛ (subst (exts σ) t) $ v} {! step congruence!} (~>→~>* (step-lambda val-v))
              ⊢ss : ⊢ ss ∈ T
              ⊢ss = t-app ⊢λ ⊢s
              ⊢ss' : ⊢ ss' ∈ T
              ⊢ss' = preservation-multi ⊢ss ss~>ss'
              σ' : ∀ {A} → (Γ , S) ∋ A → CTerm
              σ' x = (exts σ) x [ v ]
              ss'' : CTerm
              ss'' = subst σ' t
              -- need to show
              -- subst (λ x → (exts σ) x [ v ]) = subst (exts σ) t [ v ]
              ss'≡ss'' : ss' ≡ ss''
              ss'≡ss'' = {!!}
              Rss' : R T ss'
              Rss' = Eq.subst (λ z → R T z) (Eq.sym ss'≡ss'') (R-subst σ' {!!} ⊢t)

              -- Rss' = Eq.subst (λ z → R T z) (id-subst-id ss') (R-subst {Γ = ∅} id-subst (λ ()) ⊢ss')

              Rss : R T ss
              Rss = R-multistep' ⊢ss ss~>ss' Rss'
              in Rss


-- As a corollary, all well-typed closed terms are in R_T.
-- Our substitution here is the identity substitution on closed terms, which
-- trivially satisfies the hypothesis.
-- This is replaced by R-subst-id instead.
closed-term-in-R : ∀ {T t} → ⊢ t ∈ T → R T t
closed-term-in-R {T} {t} ⊢t = Eq.subst (λ z → R T z) (id-subst-id t) (R-subst {Γ = ∅} id-subst (λ ()) ⊢t)

-- Final result
normalizing : ∀ {T t} → ⊢ t ∈ T → halts t
normalizing ⊢t = R-halts (closed-term-in-R ⊢t)
