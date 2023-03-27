module Subst where

open import Base

ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → (∀ {A B} → (Γ , B) ∋ A → (Δ , B) ∋ A)
ext ρ Z = Z
ext ρ (S x) = S ρ x

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → (Term Γ → Term Δ)
rename ρ (var x) = var (ρ x)
rename ρ (ƛ t) = ƛ (rename (ext ρ) t)
rename ρ (t₁ $ t₂) = rename ρ t₁ $ rename ρ t₂

exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Term Δ)
  → (∀ {A B} → (Γ , B) ∋ A → Term (Δ , B))
exts σ Z = var Z
exts σ (S x) = rename S_ (σ x)

subst : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Term Δ) →
                  (Term Γ → Term Δ)
subst σ (var x) = σ x
subst σ (ƛ t) = ƛ (subst (exts σ) t)
subst σ (t₁ $ t₂) = subst σ t₁ $ subst σ t₂

subst-zero : ∀ {Γ B} → Term Γ → ∀ {A} → ((Γ , B) ∋ A) → Term Γ
subst-zero M Z      =  M
subst-zero M (S x)  =  var x

_[_] : ∀ {Γ B} → Term (Γ , B) → Term Γ → Term Γ
_[_] {Γ} {B} N M = subst {Γ , B} {Γ} (subst-zero M) N

-- Renaming preserves typing.
rename-preserves-typing : ∀ {Γ Δ T}
  → (σ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → (t : Term Γ)
  → Γ ⊢ t ∈ T
  → Δ ⊢ rename σ t ∈ T
rename-preserves-typing σ (var x) (t-var .x) = t-var (σ x)
rename-preserves-typing σ (ƛ t) (t-lambda H) = t-lambda (rename-preserves-typing (ext σ) t H)
rename-preserves-typing σ (t $ t₁) (t-app H H₁) = t-app (rename-preserves-typing σ t H)
                                                    (rename-preserves-typing σ t₁ H₁)

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
