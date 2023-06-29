module Subst.Subst where

open import Base
open import Subst.Sigma



-- Renaming preserves typing.
rename-preserves-typing : ∀ {Γ Δ T}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → (t : Term Γ)
  → Γ ⊢ t ∈ T
  → Δ ⊢ rename ρ t ∈ T
rename-preserves-typing ρ (var x) (t-var .x) = t-var (ρ x)
rename-preserves-typing ρ (ƛ t) (t-lambda H) = t-lambda (rename-preserves-typing (ext ρ) t H)
rename-preserves-typing ρ (t $ t₁) (t-app H H₁) = t-app (rename-preserves-typing ρ t H)
                                                    (rename-preserves-typing ρ t₁ H₁)

weakening : ∀ {Γ Δ A T} → (σ : ∀ {A} → Γ ∋ A → Term Δ)
  → (∀ {A} (x : Γ ∋ A) → Δ ⊢ σ x ∈ A)
  → (x : (Γ , A) ∋ T)
  → (Δ , A) ⊢ (exts σ x) ∈ T
weakening σ Hσ Z = t-var Z
weakening σ Hσ (S x) = rename-preserves-typing S_ (σ x) (Hσ x)

substs-lemma : ∀ {Γ Δ T t} → (σ : ∀ {A} → Γ ∋ A → Term Δ) →
  (∀ {A} (x : Γ ∋ A) → Δ ⊢ σ x ∈ A) →
  Γ ⊢ t ∈ T →
  Δ ⊢ subst σ t ∈ T
substs-lemma {t = var x} σ Hσ (t-var .x) = Hσ x
substs-lemma {t = ƛ t} σ Hσ (t-lambda Γ⊢t∈T) = t-lambda (substs-lemma (exts σ) (weakening σ Hσ) Γ⊢t∈T)
substs-lemma {t = t₁ $ t₂} σ Hσ (t-app H1 H2) = t-app (substs-lemma σ Hσ H1) (substs-lemma σ Hσ H2)

subst-zero-preserves-types : ∀ {Γ A T v} →
  Γ ⊢ v ∈ A →
  (x : (Γ , A) ∋ T) →
  Γ ⊢ subst-zero v x ∈ T
subst-zero-preserves-types Hv Z = Hv
subst-zero-preserves-types Hv (S x) = t-var x


subst-lemma : ∀ {Γ A T t v} →
  (Γ , A) ⊢ t ∈ T →
  Γ ⊢ v ∈ A →
  Γ ⊢ (t [ v ]) ∈ T
subst-lemma {Γ} {B} {T} {t} {v} H1 H2 =
  substs-lemma (subst-zero v) (subst-zero-preserves-types H2) H1

weaken-l : ∀ {Γ A t T} → Γ ⊢ t ∈ T → (Γ , A) ⊢ weaken t ∈ T
weaken-l {Γ} {A} {t} {T} ⊢t = substs-lemma (ren S_) (λ {x → t-var (S x)}) ⊢t
