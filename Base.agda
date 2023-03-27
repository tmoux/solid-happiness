module Base where

data Typ : Set where
  ⊤ : Typ
  _⇒_ : Typ → Typ → Typ
infix 30 _⇒_

data Context : Set where
  ∅ : Context
  _,_ : Context → Typ → Context


data _∋_ : Context → Typ → Set where
  Z : ∀ {Γ A}
     ---------
   → (Γ , A) ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → (Γ , B) ∋ A

-- These are well-scoped terms.
-- This makes it impossible to write a variable index that does not refer to anything.
data Term : Context → Set where
  var : ∀ {Γ A} → Γ ∋ A → Term Γ
  ƛ : ∀ {Γ A} → Term (Γ , A) → Term Γ
  _$_ : ∀ {Γ} → Term Γ → Term Γ → Term Γ



-- Closed terms are simply those that are well-formed under the empty context.
CTerm = Term ∅
example-id : CTerm
example-id = ƛ {∅} {⊤} (var Z)

data _⊢_∈_ : (Γ : Context) → Term Γ → Typ → Set where
  t-var : ∀ {Γ T} →
        (v : Γ ∋ T) →
        Γ ⊢ (var v) ∈ T
  t-app : ∀ {Γ S T f x} →
          Γ ⊢ f ∈ (S ⇒ T) →
          Γ ⊢ x ∈ S →
          Γ ⊢ (f $ x) ∈ T
  t-lambda : ∀ {Γ S T t} →
           (Γ , S) ⊢ t ∈ T →
           Γ ⊢ (ƛ {Γ} {S} t) ∈ (S ⇒ T)

