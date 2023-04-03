-- {-# OPTIONS --allow-unsolved-metas #-}

module Sigma where

open import Level
open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Function using (_∘_)

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

⟪_⟫ : ∀ {Γ Δ} → Subst Γ Δ → Term Γ → Term Δ
⟪_⟫ = subst

-- Composition of substitutions
infixr 6 _>>_
_>>_ : ∀ {Γ Δ Σ} → Subst Γ Δ → Subst Δ Σ → Subst Γ Σ
σ₁ >> σ₂ = ⟪ σ₂ ⟫ ∘ σ₁

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
   → (∀ {A} → ρ ≡ ρ′ {A})
   → ∀ {A} → ext ρ {B = B} ≡ ext ρ′ {A}
cong-ext {Γ} {Δ} {ρ} {ρ′} {B} rr {A} = extensionality λ x → lemma {x}
    where
    lemma : ∀{x : (Γ , B) ∋ A} → ext ρ x ≡ ext ρ′ x
    lemma {Z} = refl
    lemma {S y} = cong S_ (cong-app rr y)

cong-rename : ∀ {Γ Δ} → {ρ ρ' : Rename Γ Δ} {M : Term Γ} →
  (∀ {A} → ρ {A = A} ≡ ρ' {A = A}) →
  rename ρ M ≡ rename ρ' M
cong-rename {ρ = ρ} {ρ' = ρ'} {M = var x} H = cong (λ z → var (z x)) H
cong-rename {ρ = ρ} {ρ' = ρ'} {M = ƛ M} H = cong ƛ (cong-rename (cong-ext H))
cong-rename {ρ = ρ} {ρ' = ρ'} {M = N₁ $ N₂} H = cong₂ _$_ (cong-rename H) (cong-rename H)

module _ {Γ Δ : Context} where

  ren : Rename Γ Δ → Subst Γ Δ
  ren ρ x = ids (ρ x)



ren-ext : ∀ {Γ Δ}{B C : Typ} {ρ : Rename Γ Δ}
        → ren (ext ρ {B = B}) ≡ exts (ren ρ) {C}
ren-ext {Γ} {Δ} {B} {C} {ρ} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : (Γ , B) ∋ C} → (ren (ext ρ)) x ≡ exts (ren ρ) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

rename-subst-ren : ∀ {Γ Δ : Context} {M : Term Γ} {ρ : Rename Γ Δ} →
  rename ρ M ≡ ⟪ ren ρ ⟫ M
rename-subst-ren {M = var x} {ρ = ρ} = refl
rename-subst-ren {M = ƛ N} {ρ = ρ} = begin
    ƛ (rename (ext ρ) N) ≡⟨ cong ƛ (rename-subst-ren {M = N} {ρ = ext ρ}) ⟩
    ƛ (⟪ ren (ext ρ) ⟫ N) ≡⟨ cong ƛ (cong-sub (λ x → cong (λ z → z x) ren-ext) N) ⟩
    ƛ (⟪ exts (ren ρ) ⟫ N) ≡⟨⟩
    ⟪ ren ρ ⟫ (ƛ N) ∎
rename-subst-ren {M = N₁ $ N₂} {ρ = ρ} = cong₂ _$_ rename-subst-ren rename-subst-ren


compose-ext : ∀{Γ Δ Σ} {ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ} {A B}
            → ((ext ρ) ∘ (ext ρ′)) ≡ ext (ρ ∘ ρ′) {B} {A}
compose-ext = extensionality λ x → lemma {x = x}
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

commute-subst-rename : ∀ {Γ Δ} {M : Term Γ} {σ : Subst Γ Δ}
                        → (∀ {A} (x : Γ ∋ A) → Δ ⊢ σ x ∈ A) →
                        {ρ : ∀ {Γ A} → Rename Γ (Γ , A)}
    --  → (∀ {A C} {x : Γ ∋ C} → exts σ {B = A} (ρ {Γ} {A} x) ≡ rename (ρ {Γ = Δ}) (σ x))
     → ∀ {A} → subst (exts σ {B = A}) (rename ρ M) ≡ rename ρ (subst σ M)
commute-subst-rename {M = var x} = {!!}
commute-subst-rename {Γ}{Δ}{ƛ {A = A} M}{σ} Hσ {ρ} {B} =
  cong ƛ {!commute-subst-rename {σ = exts σ} {ρ = ρ'}!}
  where
  ρ' : ∀ {A Γ} → Rename Γ (Γ , A)
  ρ' {A} {∅} = λ ()
  ρ' {A} {Γ , B} = {!!}

commute-subst-rename {M = N₁ $ N₂} = {!!}
-- commute-subst-rename {M = var x} H = H
-- commute-subst-rename {Γ} {Δ} {M = ƛ {A = A} N} {σ} {ρ} {B} H = cong ƛ {!commute-subst-rename ?!}
--   where
--    ρ' : ∀ {A Γ} → Rename Γ (Γ , A)
--    ρ' {A} {∅} = λ ()
--    ρ' {A} {Γ , B} = {!ext ?!}
-- commute-subst-rename {M = N₁ $ N₂} {ρ = ρ} H = cong₂ _$_ (commute-subst-rename {M = N₁} {ρ = ρ} H) (commute-subst-rename {M = N₂} {ρ = ρ} H)
