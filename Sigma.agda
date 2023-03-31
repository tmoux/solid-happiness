module Sigma where

open import Subst

-- Prove some things about the σ-algebra.
-- Might invert the dependencies to make Subst depend on this.
-- I want to keep this to the "pure" facts about substitution, renaming, etc,
-- and leave the specific substitution lemmas to SubstFacts

Rename : Context → Context → Set
Rename Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

Subst : Context → Context → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Term Δ

ids : ∀ {Γ} → Subst Γ Γ
ids x = var x

module _ {Γ Δ : Context} where
  ⟪_⟫ : Subst Γ Δ → Term Γ → Term Δ
  ⟪_⟫ = subst

  ren : Rename Γ Δ → Subst Γ Δ
  ren ρ x = ids (ρ x)
