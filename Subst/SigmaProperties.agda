module Subst.SigmaProperties where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂; cong-app; trans)
open Eq.≡-Reasoning
open import Function using (_∘_)


open import Base
open import Subst.Sigma


---------------------
-- Congruences

-- If two substitutions are pointwise equal, then their substitutions are pointwise equal
cong-sub : ∀ {Γ Δ} {σ₁ σ₂ : Subst Γ Δ} →
    (∀ {T} → (x : Γ ∋ T) → σ₁ x ≡ σ₂ x) →
    (∀ (t : Term Γ) → subst σ₁ t ≡ subst σ₂ t)
cong-sub Hσ (var x) = Hσ x
cong-sub {Γ} {Δ} {σ₁} {σ₂} Hσ (ƛ t) = Eq.cong ƛ (f t)
    where f : ∀ {A} →
              ∀ (t : Term (Γ , A)) → subst (exts σ₁) t ≡ subst (exts σ₂) t
          f = cong-sub (λ { Z → refl ; (S x) → Eq.cong (rename S_) (Hσ x)})
cong-sub Hσ (t₁ $ t₂) rewrite cong-sub Hσ t₁ | cong-sub Hσ t₂ = refl

cong-ext : ∀ {Γ Δ} {ρ ρ′ : Rename Γ Δ} {B}
   → (∀ {A x} → ρ x ≡ ρ′ {A} x)
   → ∀ {A x} → ext ρ {B} x ≡ ext ρ′ x
cong-ext {Γ} {Δ} {ρ} {ρ′} {B} rr {A} {x} = lemma {x}
    where
    lemma : ∀ {x : (Γ , B) ∋ A} → ext ρ x ≡ ext ρ′ x
    lemma {Z} = refl
    lemma {S y} = cong S_ rr

cong-rename : ∀ {Γ Δ} → {ρ ρ' : Rename Γ Δ} {M : Term Γ} →
  (∀ {A x } → ρ {A = A} x ≡ ρ' {A = A} x) →
  rename ρ M ≡ rename ρ' M
cong-rename {ρ = ρ} {ρ' = ρ'} {M = var x} H = cong var H
cong-rename {ρ = ρ} {ρ' = ρ'} {M = ƛ M} H = cong ƛ (cong-rename (cong-ext H))
cong-rename {ρ = ρ} {ρ' = ρ'} {M = N₁ $ N₂} H = cong₂ _$_ (cong-rename H) (cong-rename H)

module _ {Γ Δ : Context} where

  ren : Rename Γ Δ → Subst Γ Δ
  ren ρ x = ids (ρ x)



ren-ext : ∀ {Γ Δ}{B C : Typ} {ρ : Rename Γ Δ}
        → ∀ {x} → ren (ext ρ {B = B}) x ≡ exts (ren ρ) x
ren-ext {Γ} {Δ} {B} {C} {ρ} {x} = lemma {x = x}
  where
  lemma : ∀ {x : (Γ , B) ∋ C} → (ren (ext ρ)) x ≡ exts (ren ρ) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

rename-subst-ren : ∀ {Γ Δ : Context} {M : Term Γ} {ρ : Rename Γ Δ} →
  rename ρ M ≡ ⟪ ren ρ ⟫ M
rename-subst-ren {M = var x} {ρ = ρ} = refl
rename-subst-ren {M = ƛ N} {ρ = ρ} = begin
    ƛ (rename (ext ρ) N) ≡⟨ cong ƛ (rename-subst-ren {M = N} {ρ = ext ρ}) ⟩
    ƛ (⟪ ren (ext ρ) ⟫ N) ≡⟨ cong ƛ (cong-sub (λ x → ren-ext {x = x}) N) ⟩
    ƛ (⟪ exts (ren ρ) ⟫ N) ≡⟨⟩
    ⟪ ren ρ ⟫ (ƛ N) ∎
rename-subst-ren {M = N₁ $ N₂} {ρ = ρ} = cong₂ _$_ rename-subst-ren rename-subst-ren


compose-ext : ∀{Γ Δ Σ} {ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ} {A B}
            → ∀ {x} → ((ext ρ) ∘ (ext ρ′)) x ≡ ext (ρ ∘ ρ′) {B} {A} x
compose-ext {x = x} = lemma {x = x}
  where
  lemma : ∀{Γ Δ Σ}{ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ} {A B} {x : (Γ , B) ∋ A}
              → ((ext ρ) ∘ (ext ρ′)) x ≡ ext (ρ ∘ ρ′) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

compose-rename : ∀ {Γ Δ Σ} {M : Term Γ} {ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ}
  → rename ρ (rename ρ′ M) ≡ rename (ρ ∘ ρ′) M
compose-rename {M = var x} = refl
compose-rename {Γ} {Δ} {Σ} {ƛ {A = A} N} {ρ} {ρ′} = cong ƛ G
  where
  G : rename (ext ρ) (rename (ext ρ′) N) ≡ rename (ext (ρ ∘ ρ′)) N
  G = begin
        rename (ext ρ) (rename (ext ρ′) N)
      ≡⟨ compose-rename {ρ = ext ρ} {ρ′ = ext ρ′} ⟩
        rename ((ext ρ) ∘ (ext ρ′)) N
      ≡⟨ cong-rename compose-ext ⟩
        rename (ext (ρ ∘ ρ′)) N
      ∎
compose-rename {M = L $ M} = cong₂ _$_ compose-rename compose-rename

ren-ren-fusion : ∀ {Γ Δ Θ} (ρ : Rename Δ Γ) (ρ′ : Rename Θ Δ) (M : Term Θ) →
  rename ρ (rename ρ′ M) ≡ rename (ρ ∘ ρ′) M
ren-ren-fusion = λ ρ ρ′ M → compose-rename
sub-ren-fusion : ∀ {Γ Δ Θ} (σ : Subst Δ Γ) (ρ : Rename Θ Δ) (M : Term Θ) →
  subst σ (rename ρ M) ≡ subst (σ ∘ ρ) M
sub-ren-fusion σ ρ (var x) = refl
sub-ren-fusion σ ρ (ƛ M) = cong ƛ (trans (sub-ren-fusion (exts σ) (ext ρ) M) G)
  where
  G : subst (λ x → exts σ (ext ρ x)) M ≡
      subst (exts (λ x → σ (ρ x))) M
  G = cong-sub (λ { Z → refl ; (S x) → refl}) M
sub-ren-fusion σ ρ (M₁ $ M₂) = cong₂ _$_ (sub-ren-fusion σ ρ M₁) (sub-ren-fusion σ ρ M₂)

ren-sub-fusion : ∀ {Γ Δ Θ} (σ : Subst Θ Δ) (ρ : Rename Δ Γ) (M : Term Θ) →
  rename ρ (subst σ M) ≡ subst (rename ρ ∘ σ) M
ren-sub-fusion σ ρ (var x) = refl
ren-sub-fusion σ ρ (ƛ M) = cong ƛ (trans (ren-sub-fusion (exts σ) (ext ρ) M) G)
  where
  G : subst (rename (ext ρ) ∘ exts σ) M ≡
      subst (exts (rename ρ ∘ σ)) M
  G = cong-sub (λ { Z → refl ; (S x) → begin
    (rename (ext ρ) ∘ exts σ) (S x) ≡⟨⟩
    rename (ext ρ) (exts σ (S x)) ≡⟨⟩
    rename (ext ρ) (rename S_ (σ x)) ≡⟨ compose-rename ⟩
    rename ((ext ρ) ∘ S_) (σ x) ≡⟨⟩
    rename (λ x → S ρ x) (σ x) ≡⟨⟩
    rename (S_ ∘ ρ) (σ x) ≡⟨ Eq.sym compose-rename ⟩
    rename S_ (rename ρ (σ x)) ≡⟨⟩
    rename S_ ((rename ρ ∘ σ) x) ∎})
    M
ren-sub-fusion σ ρ (M₁ $ M₂) = cong₂ _$_ (ren-sub-fusion σ ρ M₁) (ren-sub-fusion σ ρ M₂)


commute-subst-rename : ∀ {Γ Δ} {M : Term Γ} {σ : Subst Γ Δ}
                        {ρ : ∀ {Γ A} → Rename Γ (Γ , A)}
     → (∀ {A C} {x : Γ ∋ C} → exts σ {B = A} (ρ {Γ} {A} x) ≡ rename (ρ {Γ = Δ}) (σ x))
     → ∀ {A} → subst (exts σ {B = A}) (rename ρ M) ≡ rename ρ (subst σ M)
commute-subst-rename {M = M} {σ = σ} {ρ = ρ} H = begin
  subst (exts σ) (rename ρ M) ≡⟨ sub-ren-fusion (exts σ) ρ M ⟩
  subst ((exts σ) ∘ ρ) M ≡⟨ cong-sub (λ x → H) M ⟩
  subst (rename ρ ∘ σ) M ≡⟨ Eq.sym (ren-sub-fusion σ ρ M) ⟩
  rename ρ (subst σ M) ∎


subst-renameS-commute : ∀ {Γ₁ Γ₂ Γ₃} {σ₁ : Subst Γ₁ Γ₂} {σ₂ : Subst Γ₂ Γ₃} → ∀ {A} {x : Γ₁ ∋ A} →
    ∀ {B} → ⟪ exts σ₂ {B = B} ⟫ (rename S_ (σ₁ x)) ≡ rename S_ ((σ₁ >> σ₂) x)
subst-renameS-commute {σ₁ = σ₁} {σ₂ = σ₂} {x = x} = commute-subst-rename {M = σ₁ x} {σ = σ₂} {ρ = S_} refl

-- Composition of substitutions.
subst-comp : ∀ {Γ₁ Γ₂ Γ₃} →
  (σ₁ : Subst Γ₁ Γ₂) →
  (σ₂ : Subst Γ₂ Γ₃) →
  ∀ t → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ t) ≡ ⟪ σ₁ >> σ₂ ⟫ t
subst-comp σ₁ σ₂ (var x) = refl
subst-comp {Γ₁} σ₁ σ₂ (ƛ t) rewrite subst-comp (exts σ₁) (exts σ₂) t = cong ƛ (cong-sub H t)
  where H : ∀ {B T } → ∀ (x : (Γ₁ , B) ∋ T) → ⟪ exts σ₂ {B = B} ⟫ (exts σ₁ {B = B} x) ≡
                                 exts (σ₁ >> σ₂) x
        H Z = refl
        H (S x) = subst-renameS-commute {σ₁ = σ₁}
subst-comp σ₁ σ₂ (t₁ $ t₂) rewrite subst-comp σ₁ σ₂ t₁ |
                                   subst-comp σ₁ σ₂ t₂ = refl
