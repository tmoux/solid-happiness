module SubstFacts where

open import Subst
open import Sigma

module IdSubst where
  open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
  id-subst : ∀ {Γ A} → Γ ∋ A → Term Γ
  id-subst x = var x

  exts-id≡id : ∀ {Γ A T} → (x : (Γ , A) ∋ T) → exts id-subst x ≡ id-subst x
  exts-id≡id Z = refl
  exts-id≡id (S x) = refl

  subst-exts≡id : ∀ {Γ A} → ∀ (t : Term (Γ , A)) → subst (exts id-subst) t ≡ subst id-subst t
  subst-exts≡id = cong-sub exts-id≡id

  id-subst-id : ∀ {Γ} → ∀ (t : Term Γ) → subst id-subst t ≡ t
  id-subst-id (var x) = refl
  id-subst-id (ƛ t) rewrite subst-exts≡id t = Eq.cong ƛ (id-subst-id t)
  id-subst-id (t₁ $ t₂) rewrite id-subst-id t₁ | id-subst-id t₂ = refl




module _ where
    open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)
    open Eq.≡-Reasoning


    -- Substuting after shifting should do nothing.
    shift-subst : ∀ {Γ A} → (t : Term Γ) → (v : Term Γ) → subst (subst-zero {B = A} v) (rename {Δ = Γ , A} S_ t) ≡ t
    shift-subst {Γ} {A} t v = begin
      rename S_ t [ v ] ≡⟨⟩
      (subst (subst-zero {B = A} v) (rename S_ t) ≡⟨ cong (λ z → (subst (subst-zero v) z)) (rename-subst-ren {M = t}) ⟩
      subst (subst-zero {B = A} v) (subst (ren S_) t) ≡⟨⟩ (
      ⟪ subst-zero {B = A} v ⟫ (⟪ (ren S_) ⟫ t) ≡⟨ subst-comp _ _ t ⟩
      ⟪ ren S_ >> subst-zero {B = A} v ⟫ t ≡⟨ cong-sub (λ x → refl) t ⟩
      ⟪ IdSubst.id-subst ⟫ t ≡⟨ IdSubst.id-subst-id t ⟩
      t ∎))
