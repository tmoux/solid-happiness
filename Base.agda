module Base where

-- Let's understand the simply-typed lambda calculus.
-- Let's start by defining the types.
-- We have a base typ ⊤, and function types:
data Typ : Set where
  ⊤ : Typ
  _⇒_ : Typ → Typ → Typ
infix 30 _⇒_

-- Let's define a _context_, which is essentially a list of types:
data Context : Set where
  ∅ : Context
  _,_ : Context → Typ → Context

data _∋_ : Context → Typ → Set where
  Z : ∀ {Γ A}
   → (Γ , A) ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
    → (Γ , B) ∋ A

-- Now let's define the syntax of well-scoped terms.
-- Here we just have variables, lambda abstractions, and applications.
--
data Term : Context → Set where
  var : ∀ {Γ A} → Γ ∋ A → Term Γ
  ƛ : ∀ {Γ A} → Term (Γ , A) → Term Γ
  _$_ : ∀ {Γ} → Term Γ → Term Γ → Term Γ

-- Closed terms are simply those that are well-formed under the empty context.
CTerm = Term ∅

-- Now let's define the typing judgement.
-- Note that we define this after defining terms, instead of the "intrinsic typing" style that is sometimes presented.

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


⊢_∈_ : CTerm → Typ → Set
⊢ t ∈ T = ∅ ⊢ t ∈ T
