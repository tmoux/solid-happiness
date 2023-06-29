
module Equiv.Equiv where

-- open import Relation.Binary.PropositionalEquality as Eq

open import Base
open import Subst
open import Semantics

-- Definitional equality
data _⊢_≣_∈_ : (Γ : Context) → Term Γ → Term Γ → Typ → Set where
  q-refl : ∀ {Γ t T} → Γ ⊢ t ∈ T → Γ ⊢ t ≣ t ∈ T
  q-symm : ∀ {Γ s t T} → Γ ⊢ t ≣ s ∈ T →
              Γ ⊢ s ≣ t ∈ T
  q-trans : ∀ {Γ s t u T} →
               Γ ⊢ s ≣ t ∈ T →
               Γ ⊢ t ≣ u ∈ T →
               Γ ⊢ s ≣ u ∈ T
  q-abs : ∀ {Γ T₁ T₂} {s t : Term (Γ , T₁)} →
             (Γ , T₁) ⊢ s ≣ t ∈ T₂ →
             Γ ⊢ (ƛ {A = T₁} s) ≣ (ƛ {A = T₁} t) ∈ T₁ ⇒ T₂
  q-app : ∀ {Γ s₁ s₂ t₁ t₂ T₁ T₂} →
             Γ ⊢ s₁ ≣ t₁ ∈ T₁ ⇒ T₂ →
             Γ ⊢ s₂ ≣ t₂ ∈ T₁ →
             Γ ⊢ s₁ $ s₂ ≣ t₁ $ t₂ ∈ T₂
  q-beta : ∀ {Γ T₁ T₂} {s₁₂ t₁₂ : Term (Γ , T₁)} {s₂ t₂ : Term Γ} →
              (Γ , T₁) ⊢ s₁₂ ≣ t₁₂ ∈ T₁ →
              Γ ⊢ s₂ ≣ t₂ ∈ T₁ →
              Γ ⊢ (ƛ {A = T₁} s₁₂) $ s₂ ≣ (t₁₂ [ t₂ ]) ∈ T₂
  q-ext : ∀ {Γ T₁ T₂} {s t : Term Γ} {x : (Γ , T₁) ∋ T₁} →
             (Γ , T₁) ⊢ weaken s $ var x ≣ weaken t $ var x ∈ T₂ →
             Γ ⊢ s ≣ t ∈ T₁ ⇒ T₂

≣-weaken : ∀ {Γ s t T A} → Γ ⊢ s ≣ t ∈ T → (Γ , A) ⊢ weaken s ≣ weaken t ∈ T
≣-weaken {Γ} {s} {.s} {T} {A} (q-refl x) = q-refl (weaken-l x)
≣-weaken {Γ} {s} {t} {T} {A} (q-symm ff) = q-symm (≣-weaken ff)
≣-weaken {Γ} {s} {t} {T} {A} (q-trans ff ff₁) = q-trans (≣-weaken ff) (≣-weaken ff₁)
≣-weaken {Γ} {(ƛ t₁)} {(ƛ t₂)} {(T₁ ⇒ T₂)} {A} (q-abs ff) = q-abs {!!}
≣-weaken {Γ} {.(_ $ _)} {.(_ $ _)} {T} {A} (q-app ff ff₁) = q-app (≣-weaken ff) (≣-weaken ff₁)
≣-weaken {Γ} {.(ƛ s₁₂ $ s₂)} {.(t₁₂ [ t₂ ])} {T} {A} (q-beta {.Γ} {T₁} {T₂} {s₁₂} {t₁₂} {s₂} {t₂} ff ff₁)
  = q-beta {!!} {!!}
≣-weaken {Γ} {s} {t} {.(_ ⇒ _)} {A} (q-ext ff) = {!!}


-- Algorithmic term equivalence
mutual
  data _⊢_⇔_∈_ : (Γ : Context) → Term Γ → Term Γ → Typ → Set where


  data _⊢_↔_∈_ : (Γ : Context) → Term Γ → Term Γ → Typ → Set where
