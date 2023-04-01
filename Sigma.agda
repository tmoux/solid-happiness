module Sigma where

open import Level
open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning

open import Subst

postulate
  extensionality : ∀ {a b : Level} → Extensionality a b


-- Prove some things about the σ-algebra.
-- Might invert the dependencies to make Subst depend on this.
-- I want to keep this to the "pure" facts about substitution, renaming, etc,
-- and leave the specific substitution lemmas to SubstFacts
-- Most of this stuff is adapted from https://plfa.github.io/Substitution/

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

  cong-ext : ∀ {ρ ρ′ : Rename Γ Δ} {B}
   → (∀ {A} → ρ ≡ ρ′ {A})
   → ∀ {A} → ext ρ {B = B} ≡ ext ρ′ {A}
  cong-ext {ρ} {ρ′} {B} rr {A} = extensionality λ x → lemma {x}
    where
    lemma : ∀{x : (Γ , B) ∋ A} → ext ρ x ≡ ext ρ′ x
    lemma {Z} = refl
    lemma {S y} = cong S_ (cong-app rr y)
