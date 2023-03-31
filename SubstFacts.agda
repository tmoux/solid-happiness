{-# OPTIONS --allow-unsolved-metas #-}

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

  -- If two substitutions are pointwise equal, then their substitutions are pointwise equal
  -- We use this mainly to get around using function extensionality.
  subst-pointwise : ∀ {Γ Δ} {σ₁ σ₂ : ∀ {A} → Γ ∋ A → Term Δ} →
    (∀ {T} → (x : Γ ∋ T) → σ₁ x ≡ σ₂ x) →
    (∀ (t : Term Γ) → subst σ₁ t ≡ subst σ₂ t)
  subst-pointwise Hσ (var x) = Hσ x
  subst-pointwise {Γ} {Δ} {σ₁} {σ₂} Hσ (ƛ t) = Eq.cong ƛ (f t)
    where f : ∀ {A} →
              ∀ (t : Term (Γ , A)) → subst (exts σ₁) t ≡ subst (exts σ₂) t
          f = subst-pointwise (λ { Z → refl ; (S x) → Eq.cong (rename S_) (Hσ x)})
  subst-pointwise Hσ (t₁ $ t₂) rewrite subst-pointwise Hσ t₁ | subst-pointwise Hσ t₂ = refl

  subst-exts≡id : ∀ {Γ A} → ∀ (t : Term (Γ , A)) → subst (exts id-subst) t ≡ subst id-subst t
  subst-exts≡id = subst-pointwise exts-id≡id

  -- This was...surprisingly nontrivial.
  id-subst-id : ∀ {Γ} → ∀ (t : Term Γ) → subst id-subst t ≡ t
  id-subst-id (var x) = refl
  id-subst-id (ƛ t) rewrite subst-exts≡id t = Eq.cong ƛ (id-subst-id t)
  id-subst-id (t₁ $ t₂) rewrite id-subst-id t₁ | id-subst-id t₂ = refl




module _ where
  open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)
  open Eq.≡-Reasoning

  -- subst-[] : ∀ {S} {Γ : Context} {σ : ∀ {A} → Γ ∋ A → Term Δ} → (t : Term (Γ , S)) →
  --   subst (λ x → (exts σ) x [ v ]) t ≡ (subst (exts σ) t [ v ])
  -- subst-[] (var x) = refl
  -- subst-[] (ƛ t) rewrite subst-[] t = {!subst-[] t!}
  -- subst-[] {σ = σ} (t₁ $ t₂) rewrite subst-[] {σ = σ} t₁ | subst-[] {σ = σ} t₂ = refl

  -- subst (λ x → (exts σ) x [ v ]) = subst (exts σ) t [ v ]

  -- Lemma: Composition of renaming is equal to renaming of composition.

  -- Lemma: If renaming and substitution commute on variables, they commute on terms.

  -- Composition of substitutions.
  subst-comp : ∀ {Γ₁ Γ₂ Γ₃} →
    (σ₁ : ∀ {A} → Γ₁ ∋ A → Term Γ₂) →
    (σ₂ : ∀ {A} → Γ₂ ∋ A → Term Γ₃) →
    ∀ t → subst σ₂ (subst σ₁ t) ≡ subst (λ x → subst σ₂ (σ₁ x)) t
  subst-comp σ₁ σ₂ (var x) = refl
  subst-comp {Γ₁} σ₁ σ₂ (ƛ t) rewrite subst-comp (exts σ₁) (exts σ₂) t = cong ƛ (IdSubst.subst-pointwise H t)
    where H : ∀ {B T } → ∀ (x : (Γ₁ , B) ∋ T) → subst (exts σ₂ {B = B}) (exts σ₁ {B = B} x) ≡
                                   exts (λ y → subst σ₂ (σ₁ y)) x
          H Z = refl
          H (S x) = {! rename-subst commute!}
  subst-comp σ₁ σ₂ (t₁ $ t₂) rewrite subst-comp σ₁ σ₂ t₁ |
                                     subst-comp σ₁ σ₂ t₂ = refl

  --  ƛ (subst (λ x → subst (exts σ₂) (exts σ₁ x)) t) ≡
  --  ƛ (subst (exts (λ x → subst σ₂ (σ₁ x))) t)


  rename-subst : ∀ {Γ Δ} (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A) → (t : Term Γ) →
    rename ρ t ≡ {!!}
  rename-subst ρ t = {!!}


  -- Substuting after shifting should do nothing.
  shift-subst : ∀ {Γ A} → (t : Term Γ) → (v : Term Γ) → rename {Δ = Γ , A} S_ t [ v ] ≡ t
  shift-subst {Γ} {A} t v =
      rename S_ t [ v ] ≡⟨ {!!} ⟩
      subst σ t ≡⟨⟩ {!!}
    -- {!Eq.subst (λ z → subst σ t ≡ z) (IdSubst.id-subst-id t) !}
    where σ : ∀ {B} → (Γ ∋ B) → Term Γ
          σ x = (rename {Δ = Γ , A} S_ (var x)) [ v ]
  -- (ƛ (rename (ext S_) t) [ v ])
  -- ƛ (exts (subst-zero v) (rename exts S_) t)
  --
