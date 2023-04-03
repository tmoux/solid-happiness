module Typecheck where


open import Data.Maybe
open import Data.Maybe.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (Decidable)
-- open import Data.Bool
open import Agda.Builtin.Bool
open import Relation.Nullary.Decidable
open import Data.Empty

open import Subst hiding (subst)


arr-1 : ∀ {x₁ x₂ y₁ y₂} → x₁ ⇒ x₂ ≡ y₁ ⇒ y₂ → x₁ ≡ y₁
arr-1 refl = refl

arr-2 : ∀ {x₁ x₂ y₁ y₂} → x₁ ⇒ x₂ ≡ y₁ ⇒ y₂ → x₂ ≡ y₂
arr-2 refl = refl

infix 4 _≟_
_≟_ : Decidable {A = Typ} _≡_
⊤ ≟ ⊤ = yes refl
⊤ ≟ y ⇒ y₁ = no (λ ())
x ⇒ x₁ ≟ ⊤ = no (λ ())
x₁ ⇒ x₂ ≟ y₁ ⇒ y₂ with x₁ ≟ y₁ | x₂ ≟ y₂
... | yes p1 | yes p2 = yes (cong₂ _⇒_ p1 p2)
... | no ¬p1 | _ = no λ r → ⊥-elim (¬p1 (arr-1 r))
... | _ | no ¬p2 = no (λ r → ⊥-elim (¬p2 (arr-2 r)))

S≟S : {S : Typ} → (S ≟ S) ≡ yes refl
S≟S {⊤} = refl
S≟S {S₁ ⇒ S₂} rewrite S≟S {S₁} | S≟S {S₂} = refl


typecheck : ∀ {Γ} → Term Γ → Maybe Typ
typecheck (var {A = A} x) = just A
typecheck (ƛ {A = A} t) with typecheck t
... | just B = just (A ⇒ B)
... | nothing = nothing
typecheck (t₁ $ t₂) with typecheck t₁ | typecheck t₂
... | just (A ⇒ B) | just C with A ≟ C
...   | no ¬p = nothing
...   | yes p = just B
typecheck (t₁ $ t₂) | _ | _ = nothing

-- typechecking is correct
⊢t->typecheck : ∀ {Γ t T} → Γ ⊢ t ∈ T → typecheck t ≡ just T
⊢t->typecheck (t-var v) = refl
⊢t->typecheck (t-app {S = S} ⊢f ⊢x) rewrite ⊢t->typecheck ⊢f | ⊢t->typecheck ⊢x | S≟S {S} = refl
⊢t->typecheck (t-lambda ⊢t) rewrite ⊢t->typecheck ⊢t = refl




typecheck->⊢t : ∀ {Γ t T} → typecheck t ≡ just T → Γ ⊢ t ∈ T
typecheck->⊢t {Γ} {var x} {T} H = subst (λ z → Γ ⊢ var x ∈ z) (just-injective H) (t-var x)
typecheck->⊢t {Γ} {t = ƛ {A = A} t} {T = T} H with typecheck t | inspect typecheck t
... | just B | [ eq ] rewrite (sym (just-injective H)) = t-lambda (typecheck->⊢t eq)
-- rewrite (sym (just-injective H)) = t-lambda (typecheck->⊢t {!!})
typecheck->⊢t {Γ} {t = t₁ $ t₂} {T = T} H with typecheck t₁ | inspect typecheck t₁ | typecheck t₂ | inspect typecheck t₂
... | just x | [ eq₁ ] | just x₁ | [ eq₂ ] = t-app (typecheck->⊢t {!typecheck->⊢t eq₁!}) (typecheck->⊢t eq₂)
... | just x | [ eq ] | nothing | [ eq₁ ] = {!!}
