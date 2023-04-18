module Tests where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe
open import Data.Product

open import Base
open import Semantics
open import Eval
open import Typecheck
open import Normalization

ex-id : CTerm
ex-id = ƛ {A = ⊤} (var Z)

ex-id-T : ∅ ⊢ ex-id ∈ ⊤ ⇒ ⊤
ex-id-T = t-lambda (t-var Z)

value-ex-id : value {∅} ex-id
value-ex-id = val-lambda (var Z)

ex-id-eval : eval 5 ex-id ex-id-T ≡ done value-ex-id
ex-id-eval = refl

ex2-id : CTerm
ex2-id = (ƛ {A = ⊤ ⇒ ⊤} (var Z)) $ ex-id

ex2-id-T : ∅ ⊢ ex2-id ∈ ⊤ ⇒ ⊤
ex2-id-T = t-app (t-lambda (t-var Z)) (t-lambda (t-var Z))

ex2-id-eval : eval 5 ex2-id ex2-id-T ≡ done value-ex-id
ex2-id-eval = refl

ex-typecheck : typecheck ex-id ≡ just (⊤ ⇒ ⊤)
ex-typecheck = refl

ex2-typecheck : typecheck ex2-id ≡ just (⊤ ⇒ ⊤)
ex2-typecheck = refl


_ : ex2-id ~>* ex-id
_ = proj₁ (proj₂ (normalizing ex2-id-T))
