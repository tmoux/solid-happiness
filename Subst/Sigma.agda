module Subst.Sigma where

open import Function using (_∘_)


open import Base
-- Most of this stuff is adapted from https://plfa.github.io/Substitution/

Rename : Context → Context → Set
Rename Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

Subst : Context → Context → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Term Δ

ids : ∀ {Γ} → Subst Γ Γ
ids x = var x

module _ {Γ Δ : Context} where

  ren : Rename Γ Δ → Subst Γ Δ
  ren ρ x = ids (ρ x)



ext : ∀ {Γ Δ} → Rename Γ Δ → ∀ {B} → Rename (Γ , B) (Δ , B)
ext ρ Z = Z
ext ρ (S x) = S ρ x

rename : ∀ {Γ Δ}
  → Rename Γ Δ
  → (Term Γ → Term Δ)
rename ρ (var x) = var (ρ x)
rename ρ (ƛ t) = ƛ (rename (ext ρ) t)
rename ρ (t₁ $ t₂) = rename ρ t₁ $ rename ρ t₂

exts : ∀ {Γ Δ} → Subst Γ Δ → ∀ {B} → Subst (Γ , B) (Δ , B)
exts σ Z = var Z
exts σ (S x) = rename S_ (σ x)

subst : ∀ {Γ Δ} → Subst Γ Δ → (Term Γ → Term Δ)
subst σ (var x) = σ x
subst σ (ƛ t) = ƛ (subst (exts σ) t)
subst σ (t₁ $ t₂) = subst σ t₁ $ subst σ t₂

subst-zero : ∀ {Γ B} → Term Γ → Subst (Γ , B) Γ
subst-zero M Z      =  M
subst-zero M (S x)  =  var x

_[_] : ∀ {Γ B} → Term (Γ , B) → Term Γ → Term Γ
_[_] {Γ} {B} N M = subst {Γ , B} {Γ} (subst-zero M) N


⟪_⟫ : ∀ {Γ Δ} → Subst Γ Δ → Term Γ → Term Δ
⟪_⟫ = subst


weaken : ∀ {Γ A} → Term Γ → Term (Γ , A)
weaken {Γ} {A} = subst (ren S_)
-- Composition of substitutions
infixr 6 _>>_
_>>_ : ∀ {Γ Δ Σ} → Subst Γ Δ → Subst Δ Σ → Subst Γ Σ
σ₁ >> σ₂ = ⟪ σ₂ ⟫ ∘ σ₁
